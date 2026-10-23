-- Prove2me | Theorems.Thm_WalledBrauer_SuperSchurWeyl_theorem_7_5
-- name    : WalledBrauer.SuperSchurWeyl.theorem_7_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:16:15.838215+00:00
-- url     : https://prove2.me/theorems/28a0bf45-37ba-46c4-9a6c-59fabf2ffd14
-- title:
--   Theorem 7.5 (Sergeev, Berele–Regev) — Φ : ℂΣ_N ↠ End_g(V^{⊗N}), injective iff N < (m+1)(n+1)
-- statement:
--   Let $m, n, N \ge 0$, let $\mathfrak g = \mathfrak{gl}_{m|n}(\mathbb C)$ with natural supermodule $V$, and let
--
--   $$
--   \Phi^{m,n}_N : \mathbb C\Sigma_N \to \operatorname{End}_{\mathfrak g}(V^{\otimes N})^{\mathrm{op}}
--   $$
--
--   be the homomorphism (7.11) given by the right action (7.6) of $\Sigma_N$ on $V^{\otimes N}$ (Lemma 7.3). Then $\Phi^{m,n}_N$ is surjective: every (not necessarily homogeneous) $\mathfrak g$-supermodule endomorphism of $V^{\otimes N}$ is a linear combination of the operators $v_{\mathbf i} \mapsto v_{\mathbf i} \cdot \sigma$. Moreover $\Phi^{m,n}_N$ is injective if and only if
--
--   $$
--   N < (m+1)(n+1).
--   $$
--
--   This is super Schur–Weyl duality. In the paper $N = r + s$, and the result is the input that the walled Brauer analogue, Theorem 7.8, is reduced to.
--
--   **Formalization Note** $\mathbb C\Sigma_N$ is taken as a vector space, `Equiv.Perm (Fin N) →₀ ℂ`, and `Phi m n N` is the linear extension of `PhiDiag`; surjectivity onto $\operatorname{End}_{\mathfrak g}$ is the equality `LinearMap.range (Phi m n N) = EndG m n (allV N)`. The paper's display labels the map $\Phi^{m,n}_{r,s}$; (7.11) names it $\Phi^{m,n}_{r+s}$, and only $N = r + s$ matters.
-- source:
--   Brundan and Stroppel, Gradings on walled Brauer algebras and Khovanov's arc algebra, arXiv:1107.0999v1, p. 53, Theorem 7.5 and (7.11)

import Mathlib
import Definitions.Def_WalledBrauer_SuperSchurWeyl_Weights

namespace WalledBrauer.SuperSchurWeyl

/-- Theorem 7.5 (Sergeev, Berele–Regev; p. 53): `Φ^{m,n}_N : ℂΣ_N → End_g(V^{⊗ N})` is
surjective, and injective iff `N < (m + 1)(n + 1)` (here `N = r + s`). -/
theorem theorem_7_5 (m n N : ℕ) :
    LinearMap.range (Phi m n N) = EndG m n (allV N) ∧
    (Function.Injective (Phi m n N) ↔ N < (m + 1) * (n + 1)) := by sorry

end WalledBrauer.SuperSchurWeyl
