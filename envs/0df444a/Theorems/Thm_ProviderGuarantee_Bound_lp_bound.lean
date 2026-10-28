-- Prove2me | Theorems.Thm_ProviderGuarantee_Bound_lp_bound
-- name    : ProviderGuarantee.Bound.lp_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:42:25.042571+00:00
-- url     : https://prove2.me/theorems/bdff664b-6b4f-478b-807c-c56e453c08bc
-- title:
--   Proof of Theorem 1, pp. 37–38 — the value loss is at most the optimal value of the linear program (14)
-- statement:
--   Throughout, $D$ is a finite set of jobs with real values $v : D \to \mathbb R$ and $v(S) = \sum_{d \in S} v(d)$; there are $n$ providers $N = \{1, \dots, n\}$; $0 < \gamma_{\min} \le \gamma_{\max}$ and $\gamma \in [\gamma_{\min}, \gamma_{\max}]^n$; $\mathcal F$ is a set of allocations $A = (A_1, \dots, A_n)$ satisfying Assumption 1, and $\mathcal F_G \subseteq \mathcal F$ satisfies Assumption 2. The optimal sets are $\mathcal F^* = \arg\max_{A \in \mathcal F} \sum_i \gamma_i v(A_i)$ and $\mathcal F_G^* = \arg\max_{B \in \mathcal F_G} \sum_i \gamma_i v(B_i)$. Assume also $\mathcal F_G \ne \emptyset$.
--
--   Let $V(\gamma)$ denote the optimal value of the linear program (14) (p. 38):
--
--   $$\begin{aligned} \text{maximize}\quad & \sum_{i=1}^n \gamma_i x_i - \sum_{i=1}^n \gamma_i y_i + \sum_{i=1}^n \sum_{j=1}^n w_{ij}(\gamma_i - \gamma_j) \\ \text{subject to}\quad & \sum_{i=1}^n \gamma_i x_i + \sum_{i=1}^n \sum_{j=1}^n w_{ij}\gamma_i = 1, \\ & x_i + w_{ij} - \sum_{k=1}^n w_{kj} - y_j \le 0 \quad (i, j \in N), \qquad x, y, w \ge 0. \end{aligned}$$
--
--   Then
--
--   $$\mathbf L_\gamma(\mathcal F, \mathcal F_G) \le V(\gamma).$$
--
--   This is the bound the page obtains by solving the fractional program (13) and rescaling it, using that its constraints are homogeneous, into the linear program (14). From here on, the proof of Theorem 1 studies only the linear program, as a function of $\gamma$.
--
--   **Formalization Note** $V(\gamma)$ is `lpValue γ`, the supremum of the objective over the feasible set of (14); the milestone `lp_well_posed` states that, for $n \ge 1$, this set is non-empty and the objective is bounded by $1$ on it. No hypothesis $n \ge 1$ is needed here: with no provider the loss is $0$ and Lean's supremum of the empty set is $0$, so the inequality holds trivially.
--
--   Differences from the source:
--   - reading: the bound is stated on pp. 37–38 'for any F and F_G, given γ' → F satisfies Assumption 1, F_G ⊆ F satisfies Assumption 2, and γ ∈ [γmin, γmax]^n with 0 < γmin ≤ γmax; reason: these are the standing assumptions of §2 (pp. 7–12) under which the appendix works; the proof on pp. 35–36 uses Assumption 1-(ii), (iii), (iv), Assumption 2 and γ_j > 0, and the bound is false without them
--   - encoding: L_γ(F, F_G) is the ratio (1), which is 0/0 when max_F Σγ_i v(A_i) = 0 → valueLoss uses Lean's division, so the loss is 0 in that case; reason: only the instances where the page's ratio is undefined are affected; no hypothesis 0 < max_F is added
--   - reading: a set of jobs D (never said to be finite; v(S) is a finite sum and maxima over F are taken) → D a finite type; reason: the page writes v(S) = Σ_{d∈S} v(d) and max over F, which presuppose finitely many jobs; the paper calls D a discrete set of jobs
--   - encoding: providers N = {1, …, n} → indices i : Fin n (0, …, n−1); reason: Lean convention; a relabelling, same instances
-- source:
--   Gur, Iancu & Warnes, Value Loss in Allocation Systems with Provider Guarantees, SSRN 3351509 (version of March 24, 2020), pp. 37–38, proof of Theorem 1, (13) and (14)

import Mathlib
import Definitions.Def_ProviderGuarantee_Bound_Model

namespace ProviderGuarantee.Bound

theorem lp_bound {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} (v : D → ℝ)
    (γmin γmax : ℝ) (hγmin : 0 < γmin) (hγ : γmin ≤ γmax)
    (γ : Fin n → ℝ) (hγmem : ∀ i, γ i ∈ Set.Icc γmin γmax)
    (F FG : Set (Fin n → Finset D)) (h1 : Assumption1 F) (h2 : Assumption2 v F FG)
    (hFG : FG.Nonempty) :
    valueLoss γ v F FG ≤ lpValue γ := by sorry

end ProviderGuarantee.Bound
