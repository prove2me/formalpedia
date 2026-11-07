-- Prove2me | Theorems.Thm_RGGDetect_proposition_4
-- name    : RGGDetect.proposition_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:38:37.19679+00:00
-- url     : https://prove2.me/theorems/e5cda249-b2ab-4903-8904-981d1d351b80
-- title:
--   Proposition 4 — uniform scalar Fourier-tail bound; $B_{m,K,r}=o(1/n)$ for $K>2/\delta$
-- statement:
--   Fix integers $K\ge2$ and $B^*\ge0$. There is a constant $C$ such that for all sufficiently large $n$, uniformly over $m\le n$ and $r\le\min\{m,\lceil2mp+100\log n\rceil+B^*\}$,
--
--   $$
--   B_{m,K,r}\le C\left(\Big(\frac{npL}{\sqrt{dK}}\Big)^K+\Big(\frac{npL^2}{d}\Big)^K+\exp\Big(CnpL-\frac d{CL^2}\Big)\right).
--   $$
--
--   In particular, since $np\ge n^\delta$ and $d\gg(npL)^3$, for any fixed $K>2/\delta$, $B_{m,K,r}=o(1/n)$.
--
--   Together with Proposition 3 this makes the high-frequency Fourier remainder negligible.
--
--   **Formalization Note** In the regime (1); $L=\log(1/p)$. $C>0$ is chosen after $\delta,K,B^*$ and before the sequences. The $o(1/n)$ is $e_n/n$ with $e_n\to0$ chosen after the sequences, uniform over the same $m,r$. The factor $\sqrt{dK}$ is as printed.
--
--   Differences from the source:
--   - generalization: the standing hypotheses (1) of Theorem 1, for all n → sequences in `Regime δ p d τ`: each hypothesis for all large n; reason: the statement is asymptotic, so sequences satisfying (1) for all n are covered
--   - encoding: C a constant; o(1/n) → C > 0 chosen after δ, K, B*, before the sequences; e_n/n with e → 0 chosen after the sequences, uniform over m, r; reason: the paper's conventions (p.2)
--   - encoding: E_ρ[|η₂(ρ)|^k], ρ = ⟨z, z′⟩ → the double integral of |η₂(z, z′)|^k over independent uniform z, z′; reason: the paper identifies η₂(z, z′) with a function of ρ; same quantity
-- source:
--   Du, Mao, Sun, Wu, Xu, Sharp detection thresholds for random geometric graphs with polynomial average degrees, arXiv:2610.08517 (held version, sha256 e7bebd4a…), Proposition 4, p.27 (PDF p.29)

import Mathlib
import Definitions.Def_RGGDetect_Regime
import Definitions.Def_RGGDetect_fourierTail

open Filter Topology

namespace RGGDetect

/-- **Proposition 4** (uniform scalar Fourier-tail bound; arXiv:2610.08517, held version, sha256
e7bebd4a…, Proposition 4, p.27): fix integers `K ≥ 2` and `B* ≥ 0`. There is a constant `C` such that
for all sufficiently large `n`, uniformly over `m ≤ n` and `r ≤ min{m, ⌈2mp + 100 log n⌉ + B*}`,
`B_{m,K,r} ≤ C((npL/√(dK))^K + (npL²/d)^K + exp(CnpL - d/(CL²)))`. In particular, for any fixed
`K > 2/δ`, `B_{m,K,r} = o(1/n)`.

**Formalization Note** In the regime (1) for a fixed `δ > 0`; `L = log(1/p)`. `C > 0` is chosen
after `δ, K, B*` and before the sequences. The `o(1/n)` clause is a sequence `e → 0` (after the
sequences) with `B_{m,K,r} ≤ e_n/n` uniformly over the same `m, r`. `√(dK)` is as printed. -/
theorem proposition_4 (δ : ℝ) (hδ : 0 < δ) (K B : ℕ) (hK : 2 ≤ K) :
    (∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ → ℝ) (d : ℕ → ℕ) (τ : ℕ → ℝ), Regime δ p d τ →
      ∀ᶠ n in atTop, ∀ m r : ℕ, m ≤ n →
        r ≤ min m (⌈2 * (m : ℝ) * p n + 100 * Real.log n⌉₊ + B) →
        Btail (d n) (τ n) m K r ≤
          C * (((n : ℝ) * p n * Real.log (1 / p n) / Real.sqrt ((d n : ℝ) * K)) ^ K +
            ((n : ℝ) * p n * Real.log (1 / p n) ^ 2 / (d n : ℝ)) ^ K +
            Real.exp (C * n * p n * Real.log (1 / p n) -
              (d n : ℝ) / (C * Real.log (1 / p n) ^ 2)))) ∧
    ((K : ℝ) > 2 / δ → ∀ (p : ℕ → ℝ) (d : ℕ → ℕ) (τ : ℕ → ℝ), Regime δ p d τ →
      ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∀ᶠ n in atTop, ∀ m r : ℕ, m ≤ n →
        r ≤ min m (⌈2 * (m : ℝ) * p n + 100 * Real.log n⌉₊ + B) →
        Btail (d n) (τ n) m K r ≤ e n / n) := by sorry

end RGGDetect
