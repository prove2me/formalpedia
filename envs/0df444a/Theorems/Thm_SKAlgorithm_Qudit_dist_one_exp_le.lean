-- Prove2me | Theorems.Thm_SKAlgorithm_Qudit_dist_one_exp_le
-- name    : SKAlgorithm.Qudit.dist_one_exp_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:26:51.249237+00:00
-- url     : https://prove2.me/theorems/fd4afbc9-4c02-44db-bcb2-7644b65076ad
-- title:
--   p. 3 — d(I, exp(iH)) ≤ ‖H‖ for Hermitian H
-- statement:
--   Let $H$ be a $d \times d$ Hermitian matrix. Then, in operator norm,
--   $$d(I, \exp(iH)) = \|I - \exp(iH)\| \le \|H\|.$$
--
--   The paper derives it from the identity $d(I, \exp(iH)) = \max_E 2\sin(|E|/2)$ over the eigenvalues $E$ of $H$. It converts bounds on Hermitian generators into bounds on distances from the identity.
--
--   **Formalization Note.** Only the inequality is stated. The identity $d(I, \exp(iH)) = \max_E 2\sin(|E|/2)$ printed in the same sentence is not formalized: as printed it fails when some $|E| > \pi$ (for $H = 3\pi$ in dimension one the left side is $2$ and the right side is $-2$); the correct form has $2|\sin(E/2)|$. The exponential is `NormedSpace.exp` on complex matrices and the norm is `QAlgorithms.specNorm`.
-- source:
--   Dawson and Nielsen, The Solovay-Kitaev algorithm, arXiv:quant-ph/0505030v2, p. 3, §2, 'From this it follows easily that d(I, exp(iH)) ≤ ‖H‖'

import Mathlib
import Definitions.Def_SKAlgorithm_Qudit_Model

open scoped Matrix
open QAlgorithms

namespace SKAlgorithm.Qudit

theorem dist_one_exp_le {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian) :
    specNorm (1 - NormedSpace.exp (Complex.I • H)) ≤ specNorm H := by sorry

end SKAlgorithm.Qudit
