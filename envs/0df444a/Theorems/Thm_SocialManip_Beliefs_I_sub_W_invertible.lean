-- Prove2me | Theorems.Thm_SocialManip_Beliefs_I_sub_W_invertible
-- name    : SocialManip.Beliefs.I_sub_W_invertible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:30:17.304685+00:00
-- url     : https://prove2.me/theorems/8a44f923-820e-4b50-ace0-e2e51368297b
-- title:
--   Proof of Theorem 2 (Appendix E.2), p. 47 — under Assumption 1, I − W and I − A_DD are invertible
-- statement:
--   In the setting of Lemma 3 — agents split into Bayesians $B$ and DeGroot agents, nonnegative DeGroot weights with $\theta_i+\sum_j\alpha_{ij}=1$, signal qualities $p_i\in[1/2,1)$, and Assumption 1 (ii) strong connectedness of $G^*$, (iii) $\theta_i>0\iff p_i>1/2$ for DeGroot agents, (iv) some $p_i>1/2$ — let $\mathbf W$ be the influence matrix and $\mathbf A_{DD}=(\alpha_{ij})_{i,j\notin B}$ its DeGroot-by-DeGroot block. Then both
--   $$\mathbf I-\mathbf W\qquad\text{and}\qquad \mathbf I-\mathbf A_{DD}$$
--   are invertible matrices.
--
--   In the proof of Theorem 2 this step lets the paper solve the limiting fixed-point equation for the beliefs explicitly.
--
--   **Formalization Note** $\mathbf A_{DD}$ is the submatrix of $\alpha$ indexed by the subtype of non-Bayesian agents, and $\mathbf I$ is the identity of the matching size. Invertibility is `IsUnit` in the matrix ring. The hypotheses are those of Lemma 3, which the page invokes.
-- source:
--   Mostagir, Ozdaglar & Siderius, When Is Society Susceptible to Manipulation?, SSRN preprint 3474643 (version of 2020-06-08; Manag. Sci. 2022, doi:10.1287/mnsc.2021.4265), proof of Theorem 2 (Appendix E.2), p. 47, "Note that I − W is invertible via Lemma 3, and so has linearly independent rows, which implies that I − A_DD ⊂ I − W also has linearly independent rows, and is therefore invertible"

import Mathlib
import Definitions.Def_SocialManip_Beliefs_Setting

namespace SocialManip.Beliefs

theorem I_sub_W_invertible {n : ℕ} (B : Finset (Fin n)) (θ : Fin n → ℝ) (α : Matrix (Fin n) (Fin n) ℝ)
    (p : Fin n → ℝ) (hp : ∀ i, 1 / 2 ≤ p i ∧ p i < 1)
    (hθ : ∀ i ∉ B, 0 ≤ θ i) (hα : ∀ i ∉ B, ∀ j, 0 ≤ α i j)
    (hrow : ∀ i ∉ B, θ i + ∑ j, α i j = 1)
    (adj : Fin n → Fin n → Prop) (hadj : ∀ i ∉ B, ∀ j, adj i j ↔ 0 < α i j)
    (hA1ii : ∀ i j, i ≠ j → Relation.TransGen adj i j)
    (hA1iii : ∀ i ∉ B, (0 < θ i ↔ 1 / 2 < p i))
    (hA1iv : ∃ i, 1 / 2 < p i) :
    IsUnit (1 - W B α) ∧
      IsUnit (1 - α.submatrix (fun i : {i : Fin n // i ∉ B} => i.1)
        (fun j : {j : Fin n // j ∉ B} => j.1)) := by sorry

end SocialManip.Beliefs
