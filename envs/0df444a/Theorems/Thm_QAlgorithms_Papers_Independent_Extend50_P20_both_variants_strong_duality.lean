-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P20_both_variants_strong_duality
-- name    : QAlgorithms.Papers.Independent.Extend50.P20.both_variants_strong_duality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:12:04.005174+00:00
-- url     : https://prove2.me/theorems/fae2f4bc-e16c-4598-9255-20dcfa18acb4
-- title:
--   Attained primal and dual optima for both MPBT variants
-- statement:
--   Let $d\ge1$ and $1\le k\le N$. Use the full MPBT semidefinite programs (17)–(24). In both primal problems, $X_A\succeq0$ has trace $d^N$ and the rotated effects have sum at most $X_A\otimes I$. The probabilistic primal effects have the exact-success form $\Pi_i=P_i^+\otimes\Theta_i$, with $\Theta_i\succeq0$; the objective is $d^{-(N+k)}\sum_i\operatorname{Tr}\Theta_i$. Its dual minimizes $d^Nb$ with $\Omega\succeq0$, Bell compression at each outcome at least identity, and $bI\succeq d^{-(N+k)}\operatorname{Tr}_{\mathrm{out}}\Omega$. The deterministic primal allows all positive rotated effects, maximizing $d^{-2k}\sum_i\operatorname{Tr}(\Pi_i\sigma_i)$, where $\sigma_i=d^{-(N-k)}I_{\bar i}\otimes P_i^+$. Its dual minimizes $d^{N-2k}\|\operatorname{Tr}_{\mathrm{out}}\Omega\|_\infty$ over $\Omega\succeq\sigma_i$ for every outcome. Here $i$ is an ordered injective port tuple, $P_i^+$ uses normalized Bell projectors, $\Omega$ acts on all $N+k$ factors, and the partial trace removes all $k$ final factors. Then
--
--   $$\max P_{\mathrm{prob}}=\min D_{\mathrm{prob}},\qquad\max P_{\mathrm{det}}=\min D_{\mathrm{det}},$$
--
--   and all four extrema are attained. This identifies each unrestricted primal optimum with its dual certificate. **Formalization Note** The deterministic dual uses the equivalent scalar epigraph $bI\succeq\operatorname{Tr}_{\mathrm{out}}\Omega$, and its prefactor is a real ratio.
-- source:
--   Optimal Multi-port-based Teleportation Schemes, arXiv:2011.09256v3, PDF p. 7, Section 4 / strong duality

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P20

noncomputable section

open scoped BigOperators Matrix ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Extend50.P20

attribute [local instance] Classical.propDecidable

/-- Strong duality, PDF p.7 and p.10, proved in Appendices A-B pp.15-21.
Both unrestricted primal maxima and dual minima are attained. Omega acts
on N+k factors, correcting the introductory dimension slips; weak-duality
orientation is maximization primal <= minimization dual. -/
theorem both_variants_strong_duality (d N k : ℕ)
    (hd : 0 < d) (hk : 1 ≤ k) (hkN : k ≤ N) :
    (∃ p : ℝ, IsGreatest (probValues d N k) p ∧ IsLeast (probDualValues d N k) p) ∧
    (∃ f : ℝ, IsGreatest (detValues d N k) f ∧ IsLeast (detDualValues d N k) f) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P20

end
