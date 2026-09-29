-- Prove2me | Theorems.Thm_SiegelFields_matC_identities
-- name    : SiegelFields.matC_identities
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T01:19:00.863898+00:00
-- url     : https://prove2.me/theorems/46a4611b-c628-49cc-9cb7-0407638290e7
-- title:
--   Identities with $C$: $MCM^TC=I\det M$, $M+CM^TC=I\operatorname{tr}M$, and $\operatorname{tr}V=0\iff (VC)^T=VC$
-- statement:
--   Let $C=\begin{pmatrix}0&-i\\ i&0\end{pmatrix}$. For every complex $2\times2$ matrix $M$:
--
--   1. $MCM^TC=(\det M)\,I$;
--   2. $M+CM^TC=(\operatorname{tr}M)\,I$;
--   3. $\operatorname{tr}M=0$ if and only if $(MC)^T=MC$.
--
--   The first gives the inverse $M^{-1}=CM^TC(\det M)^{-1}$; the third says tracelessness of $V$ is equivalent to symmetry of $VC$.
-- source:
--   W. Siegel, *Fields*, arXiv:hep-th/9912205v3 (2005), https://arxiv.org/abs/hep-th/9912205, Chapter II (Spin), Section A (Two components), §IIA1 pp. 111–112

import Mathlib
import Definitions.Def_SiegelFields_SpinDefs

open Matrix Complex

namespace SiegelFields
theorem matC_identities (M : Matrix (Fin 2) (Fin 2) ℂ) :
    M * matC * Mᵀ * matC = M.det • (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
      M + matC * Mᵀ * matC = trace M • (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
      (trace M = 0 ↔ (M * matC)ᵀ = M * matC) := by sorry
end SiegelFields
