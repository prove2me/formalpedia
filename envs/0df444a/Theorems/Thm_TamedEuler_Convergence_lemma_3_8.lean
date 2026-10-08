-- Prove2me | Theorems.Thm_TamedEuler_Convergence_lemma_3_8
-- name    : TamedEuler.Convergence.lemma_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:39.407244+00:00
-- url     : https://prove2.me/theorems/0a49c208-a527-48c9-966a-71df47f124bb
-- title:
--   Lemma 3.8, p. 16 — time-discrete Burkholder–Davis–Gundy type inequality with constant p
-- statement:
--   Let $W$ be an $m$-dimensional standard $(\mathcal F_t)$-Brownian motion, $T>0$, $k,N\in\mathbb N$, and let $Z^N_l:\Omega\to\mathbb R^{k\times m}$, $l\in\{0,1,\dots,N-1\}$, be mappings such that $Z^N_l$ is $\mathcal F_{lT/N}$-measurable. With $\Delta W^N_l=W_{(l+1)T/N}-W_{lT/N}$,
--   $$\Big\|\sup_{j\in\{0,1,\dots,n\}}\Big\|\sum_{l=0}^{j-1}Z^N_l\,\Delta W^N_l\Big\|\Big\|_{L^p(\Omega;\mathbb R)}\le p\Big(\sum_{l=0}^{n-1}\sum_{i=1}^m\|Z^N_l\vec e_i\|^2_{L^p(\Omega;\mathbb R^k)}\,\frac TN\Big)^{1/2}$$
--   for all $n\in\{0,1,\dots,N\}$ and all $p\in[2,\infty)$.
--
--   This discrete martingale inequality bounds the noise part of the tamed Euler scheme in the moment estimates and in the proof of Theorem 1.1.
--
--   **Formalization Note** The paper's family indexed by $N$ is stated as "for every $N\ge1$ and every $Z$". Measurability is with respect to the $\mathbb P$-completion of $\mathcal F_{lT/N}$, a weaker hypothesis than $\mathcal F_{lT/N}$-measurability (the paper's filtration is complete). The filtration is right-continuous, as in the standing setting. Both sides are in $[0,\infty]$; no integrability is assumed.
-- source:
--   Hutzenthaler, Jentzen, Kloeden, arXiv:1010.3756v2, p. 16, Lemma 3.8, (34)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting
import Definitions.Def_TamedEuler_Convergence_Setting
import Definitions.Def_TamedEuler_Convergence_Scheme
import Definitions.Def_EthierKurtz_completedSDEPast

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace TamedEuler.Convergence

open EthierKurtz

/-- Hutzenthaler–Jentzen–Kloeden, arXiv:1010.3756v2, p. 16, Lemma 3.8 (Time discrete
Burkholder–Davis–Gundy type inequality), (34): for `k ∈ ℕ` and mappings
`Z^N_l : Ω → ℝ^{k×m}`, `l ∈ {0, …, N − 1}`, with `Z^N_l` measurable with respect to
`ℱ_{lT/N}` (here: its `P`-completion),
`‖sup_{j ∈ {0,…,n}} ‖Σ_{l=0}^{j−1} Z^N_l ΔW^N_l‖‖_{L^p(Ω;ℝ)}
  ≤ p (Σ_{l=0}^{n−1} Σ_{i=1}^m ‖Z^N_l e⃗_i‖²_{L^p(Ω;ℝ^k)} · T/N)^{1/2}`
for all `n ∈ {0, …, N}`, `N ∈ ℕ`, `p ∈ [2, ∞)`. Both sides are in `[0, ∞]`. -/
theorem lemma_3_8 {m : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 mΩ) [ℱ.IsRightContinuous]
    (T : ℝ≥0) (hT : 0 < T) (hm : 1 ≤ m)
    (W : ℝ≥0 → Ω → SDEState m) (hW : SabanisEuler.Shared.IsWienerMartingale P ℱ W)
    (k : ℕ) (hk : 1 ≤ k) (N : ℕ) (hN : 1 ≤ N)
    (Z : ℕ → Ω → Matrix (Fin k) (Fin m) ℝ)
    (hZ : ∀ l < N, Measurable[completedSDEPast P ℱ ((l : ℝ≥0) * T / N)]
      (fun ω => (Matrix.of.symm (Z l ω) : Fin k → Fin m → ℝ))) :
    ∀ n : ℕ, n ≤ N → ∀ p : ℝ, 2 ≤ p →
      (∫⁻ ω, ((Finset.range (n + 1)).sup (fun j =>
          ‖∑ l ∈ Finset.range j, matVec (Z l ω) (dW T W N l ω)‖ₑ)) ^ p ∂P) ^ (1 / p)
        ≤ ENNReal.ofReal p *
          (∑ l ∈ Finset.range n, ∑ i : Fin m,
            eLpNorm (fun ω => column (Z l ω) i) (ENNReal.ofReal p) P ^ 2
              * ENNReal.ofReal ((T : ℝ) / N)) ^ (1 / 2 : ℝ) := by sorry

end TamedEuler.Convergence
