-- Prove2me | Theorems.Thm_RGGDetect_proposition_2
-- name    : RGGDetect.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:42:07.088025+00:00
-- url     : https://prove2.me/theorems/11ac7c82-00f3-4106-b9f1-d0f268b066a9
-- title:
--   Proposition 2 — closing the posterior recursion: $Z\le C(1+\Delta/p)$
-- statement:
--   Assume the setting of Theorem 1, take cutoffs $K,M$ satisfying (67), and choose $B^*\ge4M$. There is a deterministic $0\le\theta_n=o(1)$ such that the supremum $Z$ of (80) satisfies
--
--   $$
--   Z\le C\Big(1+\frac\Delta p\Big)+\theta_nZ+o(1) \tag{82}
--   $$
--
--   for a constant $C=C(\delta,K,M)$. Adjusting the constant gives $Z\le C(1+\Delta/p)$.
--
--   This closes the cavity recurrence uniformly over the infinite class $\mathcal H_{\le2M}$.
--
--   **Formalization Note** In the regime (1); $Z$ is the supremum in $[0,\infty]$. $C>0$ is chosen after $\delta,K,M,B^*$ and before the sequences and serves both clauses; $\theta$ and the $o(1)$ sequence are chosen after the sequences.
--
--   Differences from the source:
--   - generalization: the standing hypotheses (1) of Theorem 1, for all n → sequences in `Regime δ p d τ`: each hypothesis for all large n; reason: the statement is asymptotic, so sequences satisfying (1) for all n are covered
--   - encoding: Z a real supremum; C and the adjusted constant → Z the supremum in [0, ∞]; one constant C for (82) and for Z ≤ C(1 + Δ/p); reason: Z ≤ 1/p < ∞ by (81), so the suprema agree; the larger of two constants serves both clauses
-- source:
--   Du, Mao, Sun, Wu, Xu, Sharp detection thresholds for random geometric graphs with polynomial average degrees, arXiv:2610.08517 (held version, sha256 e7bebd4a…), Proposition 2, eq. (82), p.22 (PDF p.24)

import Mathlib
import Definitions.Def_RGGDetect_Regime
import Definitions.Def_RGGDetect_Delta
import Definitions.Def_RGGDetect_Zsup

open Filter Topology

namespace RGGDetect

/-- **Proposition 2** (closing the posterior recursion; arXiv:2610.08517, held version, sha256
e7bebd4a…, Proposition 2, p.22, eq. (82)): assume the setting of Theorem 1, take cutoffs `K, M`
satisfying (67), and choose `B* ≥ 4M`. There is a deterministic `0 ≤ θ_n = o(1)` such that the
quantity `Z` of (80) satisfies `Z ≤ C(1 + Δ/p) + θ_n Z + o(1)` for a constant `C = C(δ, K, M)`.
Adjusting the constant gives `Z ≤ C(1 + Δ/p)`.

**Formalization Note** In the regime (1). `Z` is the supremum (80) in `[0, ∞]`. `C` is chosen after
`δ, K, M, B*` and before the sequences, and serves both clauses (the adjusted constant is the larger
of the two). `θ` and the `o(1)` sequence `e` are chosen after the sequences. -/
theorem proposition_2 (δ : ℝ) (hδ : 0 < δ) (K M B : ℕ) (h67a : K ≤ M) (h67b : (K : ℝ) > 2 / δ)
    (h67c : ∀ k : ℕ, 1 ≤ k → k < K → δ * (3 * (M : ℝ) + 4 - k) > 1)
    (h67d : δ * ((M : ℝ) + 4) > 1) (hB : 4 * M ≤ B) : ∃ C : ℝ, 0 < C ∧
    ∀ (p : ℕ → ℝ) (d : ℕ → ℕ) (τ : ℕ → ℝ), Regime δ p d τ →
      (∃ θ e : ℕ → ℝ, (∀ n, 0 ≤ θ n) ∧ Tendsto θ atTop (𝓝 0) ∧ Tendsto e atTop (𝓝 0) ∧
        ∀ᶠ n in atTop, Zsup n (d n) (τ n) M ≤
          ENNReal.ofReal (C * (1 + Delta n (d n) (τ n) B / p n)) +
            ENNReal.ofReal (θ n) * Zsup n (d n) (τ n) M + ENNReal.ofReal (e n)) ∧
      (∀ᶠ n in atTop, Zsup n (d n) (τ n) M ≤
        ENNReal.ofReal (C * (1 + Delta n (d n) (τ n) B / p n))) := by sorry

end RGGDetect
