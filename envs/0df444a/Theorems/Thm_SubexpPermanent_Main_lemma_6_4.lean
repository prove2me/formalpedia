-- Prove2me | Theorems.Thm_SubexpPermanent_Main_lemma_6_4
-- name    : SubexpPermanent.Main.lemma_6_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:03:23.054204+00:00
-- url     : https://prove2.me/theorems/bde57e2e-aa90-450b-8b5b-0d468fd44dec
-- title:
--   Lemma 6.4 — $F_A$ is jointly convex and shift-invariant with $\min_xF_A(\cdot,a)=\mathrm{OPT}_A(a)$; its subdifferential is the hull of $(\mu-Q+dp^{(v)},-d)$, of $\ell_1$ norm $\le2n$
-- statement:
--   Let $A$ be a nonnegative real $n\times n$ matrix with $\operatorname{per}(A)>0$, $H(x)=\max_v\log\sum_{e\ni v}e^{x_e}$, $w_e(x,a)=e^{x_e+a-H(x)}$ and $F_A(x,a)=\Phi_A(x+(a-H(x))\mathbf 1)$. Then:
--   1. $F_A$ is jointly convex on $\mathbb R^E\times\mathbb R$;
--   2. for every $a$, $F_A(x+t\mathbf 1,a)=F_A(x,a)$ for all $t\in\mathbb R$;
--   3. $\min_{x\in\mathbb R^E}F_A(x,a)=\mathrm{OPT}_A(a)$ (attained).
--
--   Fix $(x,a)$, let $\mu_e$ be the edge probabilities at weights $w(x,a)$ and $d=n-\sum_e\mu_e$. For each vertex $v$ attaining $H(x)$, the weights $w_e(x,a)$ incident to $v$ sum to $e^a$. Let $p^{(v)}_e=w_e(x,a)/e^a$ for $e\ni v$ and $0$ otherwise. For every such $v$ and every incidence matrix $Q$ of a perfect matching maximizing $\langle\log A-x,Q\rangle$ over $B$,
--   $$(\mu-Q+d\,p^{(v)},\,-d)\in\partial F_A(x,a)\qquad(26).$$
--   The full subdifferential $\partial F_A(x,a)$ is the convex hull of these vectors over all such $v$ and $Q$. For fixed $a$, the subdifferential of $F_A(\cdot,a)$ at $x$ is the convex hull of the vectors $\mu-Q+d\,p^{(v)}$, and every vector in it has $\ell_1$ norm at most $2n$. The normalization lets the §8 optimization run over an unconstrained box, and the subgradient formula drives both Lemma 6.3 and the algorithm.
--
--   Differences from the source:
--
--   - encoding: an n × n matrix (n a positive integer) → hypothesis 1 ≤ n; reason: the dimension of a matrix is positive; the §6 objects H(x) (a maximum over vertices) and 'some vertex' need a vertex
--   - encoding: vectors in ℝ^E indexed by the edges of E → functions on the subtype Edges A of pairs (i, j) in E; reason: the same space with the same coordinates
--   - encoding: min_x F_A(x, a) = OPT_A(a) → (∃ x, F A x a = OPT A a) ∧ ∀ x, OPT A a ≤ F A x a; reason: the minimum is attained and equals OPT_A(a)
--   - encoding: v attains H(x) → log ∑_{e∋v} e^{x_e} = H(x); reason: the definition of attaining the maximum
--   - encoding: ℓ1 norm of a vector g → ∑_e |g_e|; reason: the definition
-- source:
--   Kudria, Luo, Majid, Subexponential Approximation of the Permanent in Deterministic Polynomial Time, arXiv:2609.10516 (held PDF, sha256 e752b6f0…), p. 22, Lemma 6.4, eq. (26)

import Mathlib
import Definitions.Def_SubexpPermanent_Main_Objective
import Definitions.Def_SubexpPermanent_Main_Subgradient

namespace SubexpPermanent.Main

/-- Lemma 6.4 (convexity after normalization), p. 22. -/
theorem lemma_6_4 {n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hper : 0 < A.permanent) :
    ConvexOn ℝ Set.univ (fun p : (Edges A → ℝ) × ℝ => F A p.1 p.2) ∧
    (∀ (a t : ℝ) (x : Edges A → ℝ), F A (fun e => x e + t) a = F A x a) ∧
    (∀ a : ℝ, (∃ x : Edges A → ℝ, F A x a = OPT A a) ∧ ∀ x : Edges A → ℝ, OPT A a ≤ F A x a) ∧
    ∀ (x : Edges A → ℝ) (a : ℝ),
      let μ : Edges A → ℝ := edgeProbA A (logNormWeight A x a)
      let d : ℝ := (n : ℝ) - ∑ e, μ e
      let gens : Set ((Edges A → ℝ) × ℝ) :=
        {g | ∃ (v : Fin n ⊕ Fin n) (σ : Equiv.Perm (Fin n)),
          Real.log (vertexSum A x v) = Hmax A x ∧ IsPerfMatching A σ ∧
          (∀ P ∈ polytopeB A, dotProduct (logA A - x) P ≤ dotProduct (logA A - x) (incVec A σ)) ∧
          g = (μ - incVec A σ + d • pVec A x a v, -d)}
      (∀ v : Fin n ⊕ Fin n, Real.log (vertexSum A x v) = Hmax A x →
        vertexSum A (logNormWeight A x a) v = Real.exp a) ∧
      (∀ (v : Fin n ⊕ Fin n) (σ : Equiv.Perm (Fin n)),
        Real.log (vertexSum A x v) = Hmax A x → IsPerfMatching A σ →
        (∀ P ∈ polytopeB A, dotProduct (logA A - x) P ≤ dotProduct (logA A - x) (incVec A σ)) →
        (μ - incVec A σ + d • pVec A x a v, -d) ∈ subdiffJoint (F A) x a) ∧
      subdiffJoint (F A) x a = convexHull ℝ gens ∧
      subdiff (fun z => F A z a) x = convexHull ℝ (Prod.fst '' gens) ∧
      ∀ g ∈ subdiff (fun z => F A z a) x, ∑ e, |g e| ≤ 2 * (n : ℝ) := by sorry

end SubexpPermanent.Main
