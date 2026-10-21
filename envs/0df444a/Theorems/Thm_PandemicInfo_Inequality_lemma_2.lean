-- Prove2me | Theorems.Thm_PandemicInfo_Inequality_lemma_2
-- name    : PandemicInfo.Inequality.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:34:07.093492+00:00
-- url     : https://prove2.me/theorems/28924da6-de58-42db-8a8a-8e7197254dba
-- title:
--   Lemma 2, p. 18 (PDF 19) — $\lambda_1\le\lambda_2\le1/2\le4/5\le\lambda_3\le\lambda_4$, nondecreasing in $\kappa$, values at the cutoffs (26)
-- statement:
--   **Lemma 2.** For the thresholds $\lambda_1,\dots,\lambda_4$ of (19)–(22):
--
--   1. $\lambda_1\le\lambda_2\le1/2\le4/5\le\lambda_3\le\lambda_4$;
--   2. each $\lambda_i$ is nondecreasing in $\kappa$ (all other parameters fixed);
--   3. $\lambda_1(\bar\kappa_0)=\lambda_2(\underline\kappa_0)=0$ and $\lambda_3(\bar\kappa_1)=\lambda_4(\underline\kappa_1)=1$, where the cutoffs (26) are $\bar\kappa_0=\gamma G_\ell(0)$, $\underline\kappa_0=\gamma G_2(0)$, $\bar\kappa_1=\gamma G_1(1)$, $\underline\kappa_1=\gamma G_h(1)$;
--   4. the cutoffs are positive and ordered:
--   $$\bar\kappa_0>\underline\kappa_0>\bar\kappa_1>\underline\kappa_1>0.$$
--
--   The lemma is also the "Furthermore" sentence of Theorem 1.
--
--   **Formalization Note** The $\lambda_i$ are the sentinel forms of the definition file (sentinel $-1$ for $\lambda_1,\lambda_2$ and $2$ for $\lambda_3,\lambda_4$ when the defining set is empty). Monotonicity compares $\kappa<\kappa'$ for parameters satisfying the standing assumptions at $\kappa$ (they then hold at $\kappa'$). The values at the cutoffs evaluate the thresholds with $\kappa$ replaced by the cutoff; they do not require the standing assumption $\omega_\ell\kappa\ge\inf\mathcal C$ at the cutoff, since the $\lambda_i$ depend only on $\omega_\ell$, $\omega_h$ and $\kappa/\gamma$. The cutoffs are (26), $\underline\kappa_0=\gamma G_2(0)$, and not the closed form printed in the proof of Lemma 2, which does not equal $\gamma G_2(0)$. All statements assume the standing assumptions of §2 (`Params.Standing`).
-- source:
--   de Véricourt, Gurkan, Wang, Informing the Public about a Pandemic, ESMT Working Paper 20-03 (Dec. 15, 2020), p. 18 (PDF 19), Lemma 2; p. 17 (PDF 18), (26)

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_PandemicInfo_Inequality_Model
import Definitions.Def_PandemicInfo_Inequality_Reduced

namespace PandemicInfo.Inequality

/-- Lemma 2, p. 18: `λ1 ≤ λ2 ≤ 1/2 ≤ 4/5 ≤ λ3 ≤ λ4`; the thresholds are nondecreasing in `κ`;
`λ1(κ̄0) = λ2(κ_0) = 0`, `λ3(κ̄1) = λ4(κ_1) = 1`; and `κ̄0 > κ_0 > κ̄1 > κ_1 > 0`. -/
theorem lemma_2 (P : Params) (hS : P.Standing) :
    (P.lam1 ≤ P.lam2 ∧ P.lam2 ≤ 1 / 2 ∧ 4 / 5 ≤ P.lam3 ∧ P.lam3 ≤ P.lam4) ∧
    (∀ κ' : ℝ, P.κ < κ' →
      P.lam1 ≤ ({ P with κ := κ' } : Params).lam1 ∧
      P.lam2 ≤ ({ P with κ := κ' } : Params).lam2 ∧
      P.lam3 ≤ ({ P with κ := κ' } : Params).lam3 ∧
      P.lam4 ≤ ({ P with κ := κ' } : Params).lam4) ∧
    ({ P with κ := P.kap0bar } : Params).lam1 = 0 ∧
    ({ P with κ := P.kap0 } : Params).lam2 = 0 ∧
    ({ P with κ := P.kap1bar } : Params).lam3 = 1 ∧
    ({ P with κ := P.kap1 } : Params).lam4 = 1 ∧
    P.kap0 < P.kap0bar ∧ P.kap1bar < P.kap0 ∧ P.kap1 < P.kap1bar ∧ 0 < P.kap1 := by sorry

end PandemicInfo.Inequality
