-- Prove2me | Theorems.Thm_ResPCDegreeSize_Main_corollary_3_5
-- name    : ResPCDegreeSize.Main.corollary_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:26:30.218927+00:00
-- url     : https://prove2.me/theorems/64160422-9a81-499c-9621-144e8b6421ec
-- title:
--   Corollary 3.5 — kernel descent for multiplication maps
-- statement:
--   Let $Q\supseteq\mathrm{Bool}$ and $\mathcal C_D=\mathcal C_D(Q)$. Let $g_1,\dots,g_s,h_1,\dots,h_t\in\mathbb F_p[x]$ satisfy $\deg g_i\le a$ and $\deg h_j\le b$, and suppose $k\ge0$ and
--   $$b+k+pa\le D.\tag{20}$$
--   Define
--   $$M_i:V_k\to(V_D/\mathcal C_D)^t,\qquad M_if=([fg_ih_j])_{j=1}^t.\tag{21}$$
--   For $E=\mathbb F_p(\lambda_1,\dots,\lambda_s)$ these maps satisfy
--   $$\ker_EM(\lambda)\subseteq\ker_EM(\lambda^p),\tag{22}$$
--   and in particular the rank bound (19) holds: there is $c\in\mathbb F_p^s$ such that $\sum_ic_iM_i$ has rank at least $(1-1/p)$ times the rank of the stacked map.
--
--   This verifies the hypothesis of kernel descent for the operators used in the approximation argument.
--
--   Differences from the source:
--   - encoding: C_D(Q) is the set of polynomials with a degree-D derivation, "a linear subspace" → an inductive predicate PCDerivable with an extra clause making 0 derivable; CD is its carrier as a submodule of F_p[x]; reason: the source calls C_D a linear subspace, so 0 belongs to it; the clause only matters when no axiom has degree at most D, and derivation trees flatten to the source's sequences
--   - encoding: classes in V_D/C_D → classes in the quotient of the whole ring F_p[x] by C_D; reason: C_D ⊆ V_D, so V_D/C_D embeds in that quotient and every kernel and rank is unchanged; the degree bounds of the statement keep every product inside V_D
--   - encoding: E ⊗ (V_D/C_D)^t → E ⊗ (F_p[x]/C_D)^t; reason: tensoring with a field preserves the embedding of V_D/C_D, so the kernels over E agree
--   - encoding: F_p[x_1,…,x_n] → MvPolynomial (Fin n) (ZMod p) with [Fact p.Prime]; reason: relabelling of the variables; ZMod p is the field with p elements
--   - encoding: E = F_p(λ_1,…,λ_s) → the fraction field of MvPolynomial (Fin s) (ZMod p), with λ_i the images of its variables; reason: the λ_i are then algebraically independent, and any algebraically independent family generates an isomorphic field
-- source:
--   Pang, A Degree–Size Relation for Resolution over Polynomials, 2026 preprint (STOC 2027 submission #128; SHA-256 d026926040f9df67b9f5a3212fe878d8a10b50dd70b04f14b63b62a9dcb9d32f), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/128.pdf, Corollary 3.5, eqs. (20)–(22), PDF p. 6 (printed p. 5)

import Mathlib
import Definitions.Def_ResPCDegreeSize_Main_PolynomialCalculus
import Definitions.Def_ResPCDegreeSize_Main_RankMaps
open MvPolynomial

namespace ResPCDegreeSize.Main

theorem corollary_3_5 {n p s t a b k D : ℕ} [Fact p.Prime]
    (Q : Set (Poly n p)) (hQ : boolAxioms n p ⊆ Q)
    (g : Fin s → Poly n p) (h : Fin t → Poly n p)
    (hg : ∀ i, (g i).totalDegree ≤ a) (hh : ∀ j, (h j).totalDegree ≤ b)
    (h20 : b + k + p * a ≤ D) :
    LinearMap.ker (mapLam (multMaps Q D g h k)) ≤ LinearMap.ker (mapLamPow (multMaps Q D g h k)) ∧
    ∃ c : Fin s → ZMod p,
      (1 - 1 / (p : ℝ)) *
          (Module.finrank (ZMod p) (LinearMap.range (LinearMap.pi (multMaps Q D g h k))) : ℝ) ≤
        (Module.finrank (ZMod p) (LinearMap.range (∑ i, c i • multMaps Q D g h k i)) : ℝ) := by sorry

end ResPCDegreeSize.Main
