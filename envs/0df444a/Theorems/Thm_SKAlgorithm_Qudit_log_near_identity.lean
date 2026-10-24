-- Prove2me | Theorems.Thm_SKAlgorithm_Qudit_log_near_identity
-- name    : SKAlgorithm.Qudit.log_near_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T02:27:03.912488+00:00
-- url     : https://prove2.me/theorems/947e03be-4707-4179-aa35-db7e8d0b26fb
-- title:
--   p. 12 — a gate near the identity is exp(iH), H traceless Hermitian, with d(I, U) = ‖H‖ + O(‖H‖³)
-- statement:
--   Fix $d$. There are constants $\epsilon_1 > 0$ and $K > 0$ such that every $U \in SU(d)$ with $d(I, U) < \epsilon_1$ can be written $U = \exp(iH)$ with $H$ a traceless Hermitian matrix of operator norm $\|H\| < \pi$ satisfying
--   $$\big|\, d(I, U) - \|H\| \,\big| \le K \|H\|^3 ,$$
--   i.e. $d(I, U) = \|H\| + O(\|H\|^3)$.
--
--   This is the first step of the paper's balanced commutator construction in $SU(d)$: it turns a gate close to the identity into a small generator $H$ to which Lemma 2 applies.
--
--   **Formalization Note.** Two clauses are made explicit. (1) $\operatorname{tr} H = 0$: the paper does not say it on p. 12, but Lemma 2 is applied to $H$ and requires it; it holds because $\det U = 1$ and the eigenvalues of a small $H$ are small. (2) $\|H\| < \pi$: p. 3 states the expansion $d(I, \exp(iH)) = \|H\| + O(\|H\|^3)$ under the proviso that the eigenvalues of $H$ lie between $-\pi$ and $\pi$; without it, $H$ could be shifted by multiples of $2\pi$ to a large logarithm, for which the estimate holds trivially. The constants $\epsilon_1$ and $K$ may depend on $d$. The printed "U exp(iH)" is read as "U = exp(iH)".
-- source:
--   Dawson and Nielsen, The Solovay-Kitaev algorithm, arXiv:quant-ph/0505030v2, p. 12, §5.2, 'Suppose d(I, U) < ǫ. We can find Hermitian H such that U exp(iH) and d(I, U) = ‖H‖ + O(‖H‖³)'; proviso from p. 3, §2

import Mathlib
import Definitions.Def_SKAlgorithm_Qudit_Model

open scoped Matrix
open QAlgorithms

namespace SKAlgorithm.Qudit

theorem log_near_identity (d : ℕ) :
    ∃ ε₁ K : ℝ, 0 < ε₁ ∧ 0 < K ∧ ∀ U : SU d, opDist 1 U < ε₁ →
      ∃ H : Matrix (Fin d) (Fin d) ℂ, H.IsHermitian ∧ H.trace = 0 ∧ specNorm H < Real.pi ∧
        (U : Matrix (Fin d) (Fin d) ℂ) = NormedSpace.exp (Complex.I • H) ∧
        |opDist 1 U - specNorm H| ≤ K * specNorm H ^ 3 := by sorry

end SKAlgorithm.Qudit
