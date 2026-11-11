-- Prove2me | Theorems.Thm_PCSFBreach_Main_lemma_1
-- name    : PCSFBreach.Main.lemma_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:57:04.046624+00:00
-- url     : https://prove2.me/theorems/2443b626-ce86-4ee1-8230-0446dfb61bd9
-- title:
--   Lemma 1 — the (λ, µ) primal-dual algorithm in polynomial time; normal-inactive moats separate only Q; D′ is connected; yᵉ(H) = µyⁿ(H); balanced colorings
-- statement:
--   Let $\lambda>0$ and $\mu\ge 0$ be the parameters of the parametric primal-dual algorithm, $H$ its moats, $Q$ the forced pairs and $D'=D\setminus Q$.
--   1. **Polynomial time.** For rational $\lambda,\mu$ there is one polynomial-time computable function that, given the code of a rational instance, outputs the final grown forest of a run of the algorithm together with every moat $U\in H$ and its final duals $y^n_U$, $y^e_U$.
--   2. **(i)** Every moat that is current and not normal-active at some time $t\ge 0$ separates only pairs of $Q$: $\mathrm{sep}(U)\subseteq Q$.
--   3. **(ii)** Every pair of $D'$ is connected by the final grown forest.
--   4. **(iii)** $y^e(H)=\mu\cdot y^n(H)$.
--   5. **(iv)** For rational $\lambda,\mu$ a balanced coloring can be computed by one polynomial-time computable function; for every balanced coloring, with $l_i=\sum_{U\in H}a_{Ui}$ and $r_i=l_i/(\lambda\pi_i)$, the pairs with $r_i=1$ are exactly the pairs of $Q$:
--   $$a_{Ui}>0\ \Rightarrow\ r_i\le r_j\ \ (j\in\mathrm{sep}(U)),\qquad \{i: r_i=1\}=Q.$$
--
--   Items 2–5 (structural part) hold for every run with real parameters $\lambda>0$, $\mu\ge 0$. The lemma is the basic toolbox of the paper: Lemma 2, Algorithm 1 and the bifactor algorithm all start from it.
--
--   Differences from the source:
--   - generalization: an undirected graph G = (V, E) and a set D of pairs {s_i, t_i} → an edge list on the vertex set Fin n (parallel edges and loops allowed) and a pair list (repeated pairs and s_i = t_i allowed); reason: covers more instances: a simple graph with a set of distinct pairs is the case of lists without loops, parallel edges or repeats; a loop never lies in a forest and a pair with s_i = t_i is always connected
--   - reading: the primal-dual algorithm can be implemented in polynomial time → for every rational λ > 0, µ ≥ 0 there is one PolyTimeComputable M that maps the code of every rational instance to the code of the final forest of a run followed by the list of all moats of H, each once, with their final normal and extension duals (rational numbers equal to the run's); reason: Appendix B (p. 47) proves it for rational input data and rational parameters; the forest, moats and duals are the outputs the later sections use; the instance code writes |V| in unary (the input graph lists its vertices), so the output, which lists up to 2|V| − 1 moats as vertex sets, is polynomial in the input length
--   - reading: a balanced coloring can be computed efficiently → for every rational λ > 0, µ ≥ 0 there is one PolyTimeComputable M that maps the code of every rational instance to a list of entries (U, i, a_Ui) describing a balanced coloring of a run; reason: same model; the coloring is the output of the stage-wise construction on p. 6
--   - encoding: the run of the primal-dual algorithm (§2) → every record R : PDRun I with IsPDRun I λ μ R (event times 0 = t_0 < … < t_len, forests F_k, active moats A_k ⊇ normal-active moats N_k, obeying the §2 rules at every time); reason: the algorithm is continuous-time; moats and duals are determined by the instance and only the choice among simultaneously tight edges varies, so the statement is made for every run
--   - reading: (i) every normal-inactive moat → every moat U ∈ C_t, at any time t ≥ 0 at which U is not normal-active; reason: Appendix B's proof takes the time at which the moat became normal-inactive
--   - generalization: the pairs with ratio 1 are exactly the pairs in Q (for the computed balanced coloring) → for every balanced coloring of every run; reason: the proof on p. 7 uses only the balanced property; the computed coloring is a balanced coloring
--   - encoding: r_i = l_i/(λπ_i) → r_i = l_i/(λπ_i) when π_i > 0, and r_i := 1 when π_i = 0; reason: the paper removes pairs with π_i = 0 without loss of generality (p. 4); such a pair has capacity 0, is saturated by every coloring and is forced, so ratio 1 is the value consistent with 'the pairs with ratio 1 are exactly Q'; no zero-penalty instance is excluded
-- source:
--   Bosch-Calvo, Grandoni, Mátravölgyi, Breaching the 2-Approximation Barrier for Prize-Collecting Steiner Forest, STOC 2027 submission (manuscript sha256 05d9cc28…3eb3), p. 6, Lemma 1 (proofs p. 6–7 and Appendix B, pp. 47–48)

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_PCSFBreach_Main_Instance
import Definitions.Def_PCSFBreach_Main_Encoding
import Definitions.Def_PCSFBreach_Main_PrimalDual
open QAlgorithms.Complexity

namespace PCSFBreach.Main

/-- Lemma 1 (p. 6): polynomial-time implementation of the primal-dual algorithm, properties
(i)–(iii), and an efficiently computable balanced coloring whose ratio-one pairs are exactly `Q`. -/
theorem lemma_1 :
    (∀ lam μ : ℚ, 0 < lam → 0 ≤ μ →
      (∃ M : Str → Str, PolyTimeComputable M ∧ ∀ J : RatInstance, ∃ R : PDRun J.toInstance,
          IsPDRun J.toInstance lam μ R ∧ ∃ L : List (Finset (Fin J.toInstance.n) × ℚ × ℚ),
            M (encInst J) = encEdgeSet J.toInstance R.finalForest ++ encMoatList J.toInstance L ∧
            (L.map Prod.fst).Nodup ∧ (∀ U, U ∈ R.H ↔ U ∈ L.map Prod.fst) ∧
            ∀ x ∈ L, R.ynF x.1 = (x.2.1 : ℝ) ∧ R.yeF x.1 = (x.2.2 : ℝ)) ∧
      (∃ M : Str → Str, PolyTimeComputable M ∧ ∀ J : RatInstance, ∃ R : PDRun J.toInstance,
          IsPDRun J.toInstance lam μ R ∧ ∃ L : List (Finset (Fin J.toInstance.n) × J.toInstance.Pair × ℚ),
            M (encInst J) = encColoring J.toInstance L ∧ R.IsBalanced lam (coloringOf J.toInstance L))) ∧
    (∀ lam μ : ℝ, 0 < lam → 0 ≤ μ → ∀ (I : Instance) (R : PDRun I), IsPDRun I lam μ R →
      (∀ t : ℝ, 0 ≤ t → ∀ U ∈ R.moatsAt t, ¬ R.NormalActive lam t U → I.sep U ⊆ R.Q lam) ∧
      (∀ i ∈ R.D' lam, I.Connected R.finalForest (I.s i) (I.t i)) ∧
      R.YeH = μ * R.YnH ∧
      (∀ a, R.IsBalanced lam a → ∀ i, (R.ratio lam a i = 1 ↔ i ∈ R.Q lam))) := by sorry

end PCSFBreach.Main
