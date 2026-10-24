-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P11_werner_fidelity_linear_program
-- name    : QAlgorithms.Papers.Independent.Support50.P11.werner_fidelity_linear_program
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:17:40.553798+00:00
-- url     : https://prove2.me/theorems/edccff86-3879-4288-a514-d2caedb93862
-- title:
--   Proposition 10: n+1-variable Werner–Holevo fidelity LP
-- statement:
--   Fix integers $d\ge2$, $n,K\ge1$, $\alpha\in[0,1]$, and independent flags $s,p$ selecting NS and PPTp. Let $g_j,M_{ij}$ be the explicit coefficients of (A3) and the partial-trace formula. The operational optimum is the attained linear-program maximum
--   $$F^{\Omega_{s,p}}((\mathcal W^{(d,\alpha)})^{\otimes n},K)=\max_x d^n\sum_{j=0}^n\binom nj(1-\alpha)^{n-j}\alpha^jx_j,$$
--   subject to $0\le x_i\le d^{-n}$ for every $i=0,\ldots,n$, and
--   $$s\Rightarrow\sum_jg_jx_j=K^{-2},\qquad p\Rightarrow-\frac{d^{-n}}K\le\sum_jM_{ij}x_j\le\frac{d^{-n}}K\quad(0\le i\le n).$$
--   A feasible maximizing vector exists and dominates every other feasible objective. Both flags impose both constraints; neither flag gives the unrestricted forward-assisted class. Integer powers retain $0^0=1$ at the two endpoints of $\alpha$.
-- source:
--   On the power of PPT-preserving and non-signalling codes, arXiv:1406.7142v2, PDF p. 14, Proposition 10: n+1-variable Werner–Holevo fidelity LP

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P11

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P11

open QAlgorithms.Papers.Independent.Information100.P34 (choi dephasing permutationMatrix)

open QAlgorithms.Papers.Independent.Information100.P21 (pt)

open QAlgorithms.Papers.Independent.Dependency50.P09 (tensorAction)

open QAlgorithms.Papers.Independent.Information100.P76 (swapMatrix)

open QAlgorithms.Papers.Independent.Information100.P69 (replacer)

open QAlgorithms.Papers.Independent.Gap20.P19 (wernerIsometry)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.14, Proposition 10, (A4)--(A8): attained n+1-variable LP equals the
operational optimum, with NS/PPTp flags independent and neither flag giving FA. -/
theorem werner_fidelity_linear_program
    (d n K : ℕ) (hd : 2 ≤ d) (hn : 0 < n) (hK : 0 < K)
    (alpha : ℝ) (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1) (s p : Bool) :
    ∃ x : Fin (n + 1) → ℝ, WernerLPFeasible d n K s p x ∧
      optimalCodeFidelity (flagsClass s p) (piSuperop (fun _ : Fin n => wernerHolevoChannel d alpha)) K = lpObjective d n alpha x ∧
      (∀ y, WernerLPFeasible d n K s p y → lpObjective d n alpha y ≤ lpObjective d n alpha x) := by sorry

end QAlgorithms.Papers.Independent.Support50.P11

end
