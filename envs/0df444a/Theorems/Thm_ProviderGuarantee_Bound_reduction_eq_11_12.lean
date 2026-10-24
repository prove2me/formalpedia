-- Prove2me | Theorems.Thm_ProviderGuarantee_Bound_reduction_eq_11_12
-- name    : ProviderGuarantee.Bound.reduction_eq_11_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:42:33.811992+00:00
-- url     : https://prove2.me/theorems/98e8fac7-430d-4c63-83cf-9458f493b493
-- title:
--   Proof of Theorem 1, pp. 36–37 — with x_i, y_i, w_ij the loss is the ratio (12) and (11) holds: (x, y, w) is feasible for (13)
-- statement:
--   Throughout, $D$ is a finite set of jobs with real values $v : D \to \mathbb R$ and $v(S) = \sum_{d \in S} v(d)$; there are $n$ providers $N = \{1, \dots, n\}$; $0 < \gamma_{\min} \le \gamma_{\max}$ and $\gamma \in [\gamma_{\min}, \gamma_{\max}]^n$; $\mathcal F$ is a set of allocations $A = (A_1, \dots, A_n)$ satisfying Assumption 1, and $\mathcal F_G \subseteq \mathcal F$ satisfies Assumption 2. The optimal sets are $\mathcal F^* = \arg\max_{A \in \mathcal F} \sum_i \gamma_i v(A_i)$ and $\mathcal F_G^* = \arg\max_{B \in \mathcal F_G} \sum_i \gamma_i v(B_i)$.
--
--   Let $A \in \mathcal F^*$ and $B \in \mathcal F_G^*$, and define
--
--   $$x_i = v\Big(A_i \setminus \bigcup_{k=1}^n B_k\Big), \qquad y_i = v\Big(B_i \setminus \bigcup_{k=1}^n A_k\Big), \qquad w_{ij} = v(A_i \cap B_j) \qquad (i, j \in N).$$
--
--   Then:
--   1. the inequalities (11) hold: $x_i \le \sum_{k=1}^n w_{kj} - w_{ij} + y_j$ for all $i, j \in N$;
--   2. $v(A_i) = x_i + \sum_{j=1}^n w_{ij}$ for every $i$, and $v(B_j) = y_j + \sum_{i=1}^n w_{ij}$ for every $j$;
--   3. $x_i \ge 0$, $y_i \ge 0$ and $w_{ij} \ge 0$ for all $i, j$;
--   4. the value loss equals the ratio (12):
--   $$\mathbf L_\gamma(\mathcal F, \mathcal F_G) = \frac{\sum_{i=1}^n \gamma_i x_i - \sum_{i=1}^n \gamma_i y_i + \sum_{i=1}^n \sum_{j=1}^n w_{ij}(\gamma_i - \gamma_j)}{\sum_{i=1}^n \gamma_i x_i + \sum_{i=1}^n \sum_{j=1}^n w_{ij}\gamma_i}.$$
--
--   Together, (1)–(4) say that $(x, y, w)$ is a feasible point of the fractional linear program (13) whose objective value is the loss. This turns the combinatorial question into a linear-fractional one.
--
--   Differences from the source:
--   - reading: Lemma 1 is stated 'for any fixed F and F_G' → F satisfies Assumption 1, F_G ⊆ F satisfies Assumption 2, and γ ∈ [γmin, γmax]^n with 0 < γmin ≤ γmax; reason: these are the standing assumptions of §2 (pp. 7–12) under which the appendix works; the proof on pp. 35–36 uses Assumption 1-(ii), (iii), (iv), Assumption 2 and γ_j > 0, and the lemma is false without them
--   - reading: the page uses (11) and the decompositions of v(A_i), v(B_j) to call (13), which imposes x, y, w ≥ 0, an upper bound on L_γ → the non-negativity x_i, y_i, w_ij ≥ 0 is stated as part of the conclusion; reason: the page's step needs (x, y, w) feasible for (13); non-negativity holds because optimal allocations hold no job of negative value (Assumption 1-(iii), Assumption 2, γ > 0) and is a conclusion, not an added hypothesis on v
--   - encoding: (12) equals L_γ(F, F_G), both sides being 0/0 when max_F Σγ_i v(A_i) = 0 → equality of Lean's quotients, both 0 in that case; reason: Lean's division by zero; the denominator of (12) is Σγ_i v(A_i) = max_F, so the two sides are undefined on the page exactly together
--   - reading: a set of jobs D (never said to be finite; v(S) is a finite sum and maxima over F are taken) → D a finite type; reason: the page writes v(S) = Σ_{d∈S} v(d) and max over F, which presuppose finitely many jobs; the paper calls D a discrete set of jobs
--   - encoding: providers N = {1, …, n} → indices i : Fin n (0, …, n−1); reason: Lean convention; a relabelling, same instances
-- source:
--   Gur, Iancu & Warnes, Value Loss in Allocation Systems with Provider Guarantees, SSRN 3351509 (version of March 24, 2020), pp. 36–37, proof of Theorem 1, (11) and (12)

import Mathlib
import Definitions.Def_ProviderGuarantee_Bound_Model

namespace ProviderGuarantee.Bound

theorem reduction_eq_11_12 {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} (v : D → ℝ)
    (γmin γmax : ℝ) (hγmin : 0 < γmin) (hγ : γmin ≤ γmax)
    (γ : Fin n → ℝ) (hγmem : ∀ i, γ i ∈ Set.Icc γmin γmax)
    (F FG : Set (Fin n → Finset D)) (h1 : Assumption1 F) (h2 : Assumption2 v F FG)
    (A B : Fin n → Finset D) (hA : IsOptimal γ v F A) (hB : IsOptimal γ v FG B) :
    let x : Fin n → ℝ := fun i => val v (A i \ Finset.univ.biUnion B)
    let y : Fin n → ℝ := fun i => val v (B i \ Finset.univ.biUnion A)
    let w : Fin n → Fin n → ℝ := fun i j => val v (A i ∩ B j)
    (∀ i j, x i ≤ ∑ k, w k j - w i j + y j) ∧
    (∀ i, val v (A i) = x i + ∑ j, w i j) ∧
    (∀ j, val v (B j) = y j + ∑ i, w i j) ∧
    (∀ i, 0 ≤ x i) ∧ (∀ i, 0 ≤ y i) ∧ (∀ i j, 0 ≤ w i j) ∧
    valueLoss γ v F FG =
      (∑ i, γ i * x i - ∑ i, γ i * y i + ∑ i, ∑ j, w i j * (γ i - γ j)) /
        (∑ i, γ i * x i + ∑ i, ∑ j, w i j * γ i) := by sorry

end ProviderGuarantee.Bound
