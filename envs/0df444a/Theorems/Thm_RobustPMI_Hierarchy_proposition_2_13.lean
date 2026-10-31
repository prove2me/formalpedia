-- Prove2me | Theorems.Thm_RobustPMI_Hierarchy_proposition_2_13
-- name    : RobustPMI.Hierarchy.proposition_2_13
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-30T23:53:07.718121+00:00
-- url     : https://prove2.me/theorems/e826b806-db71-4c6e-9cac-1dd95c7d825f
-- title:
--   Proposition 2.13 (p. 9) — $\mathscr L_S(\Sigma_0)=\operatorname{tr}(Z_0M_d(S))\ge0$ and $\mathscr L_S((\Sigma_1,G)_m)=\operatorname{tr}(Z_1M_d(GS))\ge0$
-- statement:
--   Let $S=(S_\alpha)_{\alpha\in\mathbb N^n}$ be a sequence of real $m\times m$ matrices and let $G(x)\in\mathbb S[x]^q$. Recall the Riesz functional $\mathscr L_S(F)=\sum_{\alpha}\operatorname{tr}(F_\alpha S_\alpha)$, the $d$-th order moment matrix $M_d(S)$ (block rows/columns indexed by $\mathbb N^n_d$, $(\alpha,\beta)$-block $S_{\alpha+\beta}$) and the $d$-th order localizing matrix $M_d(GS)$ (with $(\alpha,\beta)$-block $\sum_{\gamma} S_{\alpha+\beta+\gamma}\otimes G_\gamma$).
--
--   Proposition 2.13 of the source states that for SOS matrices written in Gram form $\Sigma_0=(u_d\otimes I_m)^\top Z_0(u_d\otimes I_m)$ and $\Sigma_1=(u_d\otimes I_{mq})^\top Z_1(u_d\otimes I_{mq})$,
--   $$\mathscr L_S(\Sigma_0)=\operatorname{tr}(Z_0M_d(S)),\qquad \mathscr L_S((\Sigma_1,G)_m)=\operatorname{tr}(Z_1M_d(GS)).$$
--   This item records the consequence used for weak duality ("$\mathscr M^m_k(G)$ is the dual cone of $\mathscr Q^m_k(G)$", p. 9):
--
--   1. If $\Sigma_0=T_0^\top T_0$ for an $l\times m$ polynomial matrix $T_0$ whose entries have degree at most $d$, and $M_d(S)\succeq0$, then $\mathscr L_S(\Sigma_0)\ge 0$.
--   2. If $\Sigma_1=T_1^\top T_1$ for an $l\times mq$ polynomial matrix $T_1$ whose entries have degree at most $d$, and $M_d(GS)\succeq0$, then $\mathscr L_S((\Sigma_1,G)_m)\ge0$, where $(A,B)_m=\operatorname{tr}_m(A^\top(I_m\otimes B))$.
--
--   Here $Z_0$ (resp. $Z_1$) is the PSD Gram matrix $\sum_r w_rw_r^\top$ whose vectors $w_r$ collect the coefficients of the rows of $T_0$ (resp. $T_1$), so the nonnegativity follows from $\operatorname{tr}(Z M)\ge0$ for PSD $Z$ and $M$. No symmetry of $S_\alpha$ or of $G$ is needed for this direction.
-- source:
--   Guo, Wang, A moment-SOS hierarchy for robust polynomial matrix inequality optimization with SOS-convexity, arXiv:2304.12628v5, p. 9, Proposition 2.13 (and the remark after it that M^m_k(G) is the dual cone of Q^m_k(G))

import Mathlib
import Definitions.Def_RobustPMI_Hierarchy_Model

namespace RobustPMI.Hierarchy

open Matrix

/-- Proposition 2.13 (p. 9), nonnegativity form: if `Σ₀ = T₀ᵀ T₀` with all entries of `T₀` of
degree `≤ d` and `M_d(S) ⪰ 0`, then `𝓛_S(Σ₀) = tr(Z₀ M_d(S)) ≥ 0`; if `Σ₁ = T₁ᵀ T₁` with all
entries of `T₁` of degree `≤ d` and `M_d(GS) ⪰ 0`, then `𝓛_S((Σ₁, G)_m) = tr(Z₁ M_d(GS)) ≥ 0`. -/
theorem proposition_2_13 {n m q : ℕ} (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ))
    (S : MatSeq (Fin n) (Fin m)) :
    (∀ (d l : ℕ) (T : Matrix (Fin l) (Fin m) (MvPolynomial (Fin n) ℝ)),
      (∀ i j, (T i j).totalDegree ≤ d) → (momentMat d S).PosSemidef → 0 ≤ riesz S (Tᵀ * T)) ∧
    (∀ (d l : ℕ) (T : Matrix (Fin l) (Fin m × Fin q) (MvPolynomial (Fin n) ℝ)),
      (∀ i j, (T i j).totalDegree ≤ d) → (locMat d G S).PosSemidef →
        0 ≤ riesz S (pairM (Tᵀ * T) G)) := by sorry

end RobustPMI.Hierarchy
