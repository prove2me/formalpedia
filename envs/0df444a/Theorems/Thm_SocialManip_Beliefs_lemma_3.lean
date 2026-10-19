-- Prove2me | Theorems.Thm_SocialManip_Beliefs_lemma_3
-- name    : SocialManip.Beliefs.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:30:10.338994+00:00
-- url     : https://prove2.me/theorems/bb59e6b8-f988-488a-8b4e-5f3c09a895a2
-- title:
--   Lemma 3, p. 45 — under Assumption 1, the spectral radius of the influence matrix W is strictly less than 1
-- statement:
--   Let $n$ agents be split into a set $B$ of Bayesian agents and the remaining DeGroot agents. Each DeGroot agent $i$ has a self-weight $\theta_i\ge0$ and neighbour weights $\alpha_{ij}\ge0$ with
--   $$\theta_i+\sum_{j=1}^n\alpha_{ij}=1,$$
--   and every agent has a signal quality $p_i\in[1/2,1)$. Let $\mathbf W$ be the influence matrix: zero rows for Bayesian agents and row $(\alpha_{ij})_j$ for each DeGroot agent. Let $G^*$ be a directed graph on the agents in which a DeGroot agent $i$ links to $j$ exactly when $\alpha_{ij}>0$ (the links of Bayesian agents are arbitrary). Assume the network parts of Assumption 1:
--
--   1. (ii) *strong connectedness*: for any two distinct agents $i,j$ there is a directed path from $i$ to $j$ in $G^*$;
--   2. (iii) *irrelevance of noise*: for every DeGroot agent $i$, $\theta_i>0$ if and only if $p_i>1/2$;
--   3. (iv) *identifiability*: some agent has $p_i>1/2$.
--
--   Then the spectral radius of $\mathbf W$, viewed as a complex matrix, is strictly less than one:
--   $$\rho(\mathbf W)<1 .$$
--
--   This is the linear-algebra core of the belief characterization: it makes $\mathbf I-\mathbf W$ invertible and the DeGroot recursion stable, so that the limit $(\mathbf I-\mathbf W)^{-1}(\cdot)$ in Theorem 2 exists.
--
--   **Formalization Note** The page states Lemma 3 without hypotheses, but its proof uses the row sums and Assumption 1 (ii)–(iv), standing assumptions of §2 and §3.2; they are written as hypotheses. The spectral radius is Mathlib's `spectralRadius ℂ` of the complexified matrix, the supremum of the moduli of its eigenvalues, valued in $[0,\infty]$. "A path from $i$ to $j$ and from $j$ to $i$" is stated as a path for every ordered pair of distinct agents.
-- source:
--   Mostagir, Ozdaglar & Siderius, When Is Society Susceptible to Manipulation?, SSRN preprint 3474643 (version of 2020-06-08; Manag. Sci. 2022, doi:10.1287/mnsc.2021.4265), Lemma 3 (Appendix E.1), p. 45; standing assumptions: θ_i + Σ_j α_ij = 1 (p. 7), Assumption 1 (ii)–(iv) (pp. 10–11)

import Mathlib
import Definitions.Def_SocialManip_Beliefs_Setting

namespace SocialManip.Beliefs

theorem lemma_3 {n : ℕ} (B : Finset (Fin n)) (θ : Fin n → ℝ) (α : Matrix (Fin n) (Fin n) ℝ)
    (p : Fin n → ℝ) (hp : ∀ i, 1 / 2 ≤ p i ∧ p i < 1)
    (hθ : ∀ i ∉ B, 0 ≤ θ i) (hα : ∀ i ∉ B, ∀ j, 0 ≤ α i j)
    (hrow : ∀ i ∉ B, θ i + ∑ j, α i j = 1)
    (adj : Fin n → Fin n → Prop) (hadj : ∀ i ∉ B, ∀ j, adj i j ↔ 0 < α i j)
    (hA1ii : ∀ i j, i ≠ j → Relation.TransGen adj i j)
    (hA1iii : ∀ i ∉ B, (0 < θ i ↔ 1 / 2 < p i))
    (hA1iv : ∃ i, 1 / 2 < p i) :
    spectralRadius ℂ ((W B α).map (algebraMap ℝ ℂ)) < 1 := by sorry

end SocialManip.Beliefs
