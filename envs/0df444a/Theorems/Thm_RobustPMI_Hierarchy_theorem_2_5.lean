-- Prove2me | Theorems.Thm_RobustPMI_Hierarchy_theorem_2_5
-- name    : RobustPMI.Hierarchy.theorem_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:00.138434+00:00
-- url     : https://prove2.me/theorems/95574e4b-6fee-4eb0-8a6b-5ba309342148
-- title:
--   Theorem 2.5, p. 6 — Scherer–Hol: under Assumption 2, F ≻ 0 on 𝒳 implies F = Σ₀ + (Σ₁, G)_m
-- statement:
--   This is the matrix Positivstellensatz of Scherer and Hol, as quoted by Guo and Wang.
--
--   Let $G(x)$ be a $q\times q$ symmetric polynomial matrix, $\mathcal X=\{x\in\mathbb R^n:G(x)\succeq0\}$, and suppose Assumption 2 holds: there are $r\in\mathbb R$ and an SOS matrix $\Sigma(x)$ with $r^2-\|x\|^2-\langle\Sigma(x),G(x)\rangle$ a sum of squares. Let $F(x)\in\mathbb S[x]^m$ be positive definite at every point of $\mathcal X$. Then there exist SOS polynomial matrices $\Sigma_0(x)\in\mathbb S[x]^m$ and $\Sigma_1(x)\in\mathbb S[x]^{mq}$ such that
--   $$F(x)=\Sigma_0(x)+(\Sigma_1(x),G(x))_m .$$
--
--   Here $(A,B)_m=\operatorname{tr}_m(A^{\intercal}(I_m\otimes B))$. The certificate lies in the matrix quadratic module $\mathcal Q^m(G)=\bigcup_k\mathcal Q^m_k(G)$; no bound on the degrees is asserted. In the convergence proof it shows that the moment vector of a strictly feasible point becomes feasible for the dual relaxation (4.5) once the relaxation order is large enough.
--
--   **Formalization Note** The symmetry of $G$ and $F$ (they lie in $\mathbb S[x]^q$, $\mathbb S[x]^m$ by the paper's notation) is stated as a hypothesis. $\Sigma_1$ is indexed by pairs (block index in $\{1,\dots,m\}$, index in $\{1,\dots,q\}$).
-- source:
--   Guo, Wang, A moment-SOS hierarchy for robust polynomial matrix inequality optimization with SOS-convexity, arXiv:2304.12628v5, p. 6, Theorem 2.5 (citing Scherer–Hol 2006, Corollary 1)

import Mathlib
import Definitions.Def_RobustPMI_Hierarchy_Model

namespace RobustPMI.Hierarchy

open MvPolynomial

/-- Theorem 2.5 (p. 6), Scherer–Hol: under Assumption 2, a symmetric polynomial matrix `F(x)` that is
positive definite on `𝒳` equals `Σ₀(x) + (Σ₁(x), G(x))_m` for SOS matrices `Σ₀ ∈ 𝕊[x]^m`,
`Σ₁ ∈ 𝕊[x]^{mq}` (no degree bound). -/
theorem theorem_2_5 {n m q : ℕ} (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ))
    (hG : G.IsSymm) (h2 : Assumption2 G)
    (F : Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ)) (hF : F.IsSymm)
    (hpd : ∀ x ∈ Xset G, (F.map (eval x)).PosDef) :
    ∃ (Sig0 : Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ))
      (Sig1 : Matrix (Fin m × Fin q) (Fin m × Fin q) (MvPolynomial (Fin n) ℝ)),
      IsSOSMat Sig0 ∧ IsSOSMat Sig1 ∧ F = Sig0 + pairM Sig1 G := by sorry

end RobustPMI.Hierarchy
