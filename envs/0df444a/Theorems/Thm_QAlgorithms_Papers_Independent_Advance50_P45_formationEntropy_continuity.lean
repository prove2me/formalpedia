-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P45_formationEntropy_continuity
-- name    : QAlgorithms.Papers.Independent.Advance50.P45.formationEntropy_continuity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:19:33.580815+00:00
-- url     : https://prove2.me/theorems/ceb342c7-ed7b-4fd6-be68-1ce3186f8621
-- title:
--   Continuity of entanglement of formation
-- statement:
--   Let $A,B$ be nonzero finite-dimensional quantum systems, with dimensions $d_A,d_B$, and put $d=\min\{d_A,d_B\}$. Let $\rho_{AB},\sigma_{AB}$ be arbitrary positive semidefinite trace-one operators. Suppose
--   $$
--   \tfrac12\|\rho_{AB}-\sigma_{AB}\|_1\le\varepsilon,
--   \qquad 0<\varepsilon\le 1-\frac{\sqrt{2d-1}}{d},
--   \qquad \delta=\sqrt{\varepsilon(2-\varepsilon)},
--   $$
--   where the norm is the Schatten trace norm. For a state $\omega_{AB}$ define its entanglement of formation in bits by
--   $$
--   E_F(\omega_{AB})=
--   \inf_{\omega_{AB}=\sum_{j=1}^{m}p_j|\psi_j\rangle\langle\psi_j|}
--   \sum_{j=1}^{m}p_j H\!\left(\operatorname{Tr}_A|\psi_j\rangle\langle\psi_j|\right).
--   $$
--   The infimum ranges over all finite lengths $m$, all probability weights $p_j$, and all unit vectors $\psi_j$ with the prescribed barycenter. Here $H$ is the von Neumann entropy with base-two logarithms. Then
--   $$
--   \bigl|E_F(\rho_{AB})-E_F(\sigma_{AB})\bigr|
--   \le \delta\log_2(d-1)+h_2(\delta),
--   $$
--   where $h_2(t)=-t\log_2t-(1-t)\log_2(1-t)$ with the zero convention.
--
--   This bounds variation of the unrestricted pure-state convex roof using only the smaller subsystem dimension and an upper bound on trace distance.
--
--   **Formalization Note** The accepted convex roof uses the first marginal. Exchanging both product coordinates makes this marginal exactly the source's $B$ marginal in every decomposition.
-- source:
--   Optimal uniform continuity bound for conditional entropy of classical--quantum states, arXiv:1909.01755v2, PDF p. 5, Corollary 2, Eqs. (26)–(28)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P45

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Advance50.P45

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P56 (cqBlock)

/-- Corollary 2, PDF p.5, Eqs.(26)–(28): continuity of the unrestricted
pure-ensemble convex roof for arbitrary finite bipartite density states.
Here d=min(card A,card B) and delta=sqrt(epsilon*(2-epsilon)) are computed,
not supplied as independent parameters. Epsilon merely bounds trace distance;
no sharpness claim is made for this corollary. -/
theorem formationEntropy_continuity {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] [DecidableEq A] [DecidableEq B]
    (rho sigma : Matrix (A × B) (A × B) ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hupper : epsilon ≤ 1 -
      Real.sqrt (2 * (min (Fintype.card A) (Fintype.card B) : ℝ) - 1) /
        (min (Fintype.card A) (Fintype.card B) : ℝ))
    (hdistance : traceNorm (rho - sigma) / 2 ≤ epsilon) :
    |formationEntropy rho - formationEntropy sigma| ≤
      Real.sqrt (epsilon * (2 - epsilon)) *
        Real.logb 2 ((min (Fintype.card A) (Fintype.card B) : ℝ) - 1) +
        binEntropy2 (Real.sqrt (epsilon * (2 - epsilon))) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P45

end
