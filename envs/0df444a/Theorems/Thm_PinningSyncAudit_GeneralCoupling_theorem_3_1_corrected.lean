-- Prove2me | Theorems.Thm_PinningSyncAudit_GeneralCoupling_theorem_3_1_corrected
-- name    : PinningSyncAudit.GeneralCoupling.theorem_3_1_corrected
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:51:52.174851+00:00
-- url     : https://prove2.me/theorems/ee774951-ed9f-4232-9631-012f560746f9
-- title:
--   Theorem 3.1 (corrected: full symmetric coupling term)
-- statement:
--   Let $N,n\ge1$, and let $f:\mathbb R^n\times[0,\infty)\to\mathbb R^n$ be jointly continuously differentiable. Let $K,\Gamma\in\mathbb R^{n\times n}$ be constant real matrices and $c\in\mathbb R$. Assume uniformly for every $t\ge0$ and $u,v\in\mathbb R^n$ that
--
--   $$
--   (u-v)^T(f(u,t)-f(v,t))\le (u-v)^TK\Gamma(u-v).
--   $$
--
--   Let $G\in\mathbb R^{N\times N}$ have nonnegative off-diagonal entries and zero row sums. Its directed graph, with edge $j\to i$ exactly when $i\ne j$ and $G_{ij}>0$, is strongly connected. Let the feedback gains be $d_i\ge0$ and put $D=\operatorname{diag}(d)$. Let $\xi_i>0$, $\Xi=\operatorname{diag}(\xi)$ and $\widehat G=(\Xi G+G^T\Xi)/2$, and assume all row sums of $\widehat G$ are zero, as for the witnesses in Lemma 2.12. Suppose the explicit corrected matrix satisfies
--
--   $$
--   M_*=\Xi\otimes\frac{K\Gamma+\Gamma^TK^T}{2}
--   +\frac c2\big[(\Xi G)\otimes\Gamma+(G^T\Xi)\otimes\Gamma^T\big]
--   -c(\Xi D)\otimes\frac{\Gamma+\Gamma^T}{2}<0.
--   $$
--
--   For every initial reference state $s_0\in\mathbb R^n$ and network state $x_0\in(\mathbb R^n)^N$, there exist trajectories $s,x$ on all of $[0,\infty)$ with $s(0)=s_0$, $x(0)=x_0$, satisfying
--
--   $$
--   \dot s=f(s,t),\qquad
--   \dot x_i=f(x_i,t)+c\sum_{j=1}^N G_{ij}\Gamma x_j-cd_i\Gamma(x_i-s).
--   $$
--
--   Moreover, every global solution pair of these equations satisfies
--
--   $$
--   \forall i\in\{1,\ldots,N\},\qquad
--   \lim_{t\to\infty}\|x_i(t)-s(t)\|=0.
--   $$
--
--   This is a sufficient criterion for global synchronization with a moving reference trajectory, retaining arbitrary real inner coupling $\Gamma$. No symmetry, positivity or commutation of $\Gamma$, boundedness of trajectories, or global two-sided Lipschitz property of $f$ is assumed. The printed (3.2) is not used as the hypothesis: it omits the term $\frac c4(\Xi G-G^T\Xi)\otimes(\Gamma-\Gamma^T)$ and fails on the exact example in the differences below. The existing Proved symmetric-$\Gamma$ result is prior art, not a proof of this general criterion.
--
--   **Formalization Note** Strict negative definiteness is positive definiteness of $-M_*$. Convergence uses the published vector-limit predicate at each vertex. Existence and convergence are separate conjuncts; existence is concluded rather than assumed. The source's pinning selection is recovered by taking $d_{q_i}>0$ on its $l=\lfloor\delta N\rfloor$ selected vertices and zero on the others, including $l=0$.
--
--   Differences from the source:
--   - correction: the printed matrix M₀ in (3.2) uses c Ĝ ⊗ sym(Γ) → M* uses (c/2)[(ΞG) ⊗ Γ + (GᵀΞ) ⊗ Γᵀ], adding exactly (c/4)(ΞG − GᵀΞ) ⊗ (Γ − Γᵀ); reason: the printed claim is false: N=3, n=2, δ=1/2, c=1, f=0, K=0, s=0, Ξ=I₃, G=[[-1,1,0],[0,-1,1],[1,0,-1]], d=(19/12,0,0), Γ=[[1,5],[-5,1]] satisfy every source assumption; −((G+Gᵀ)/2−D) has leading principal minors 31/12, 7/3, 19/16, so M₀<0, but (G−D)⊗Γ has an eigenvalue with real part (−17+5√15)/8>0 and a global real growing solution
--   - generalization: 0 < δ < 1 and l = floor(δN) distinct selected vertices with positive gains, zero elsewhere → any nonnegative gain vector d, with no restriction on its support; reason: every source selection extends to such a vector; arbitrary support and even all vertices pinned also satisfy the same corrected criterion, without changing its proof or imposing any new condition
--   - encoding: positive numbers N,n of vertices and state coordinates, and continuous time t ≥ 0 → N > 0 and n > 0 with Fin indices, real-valued trajectories and derivatives within Ici 0; reason: indices are relabeled from 1-based to 0-based; the derivative at zero is from the right, and negative-time extensions are irrelevant
--   - encoding: Ξ is a positive diagonal witness furnished by Lemma 2.12, with symmetric Ĝ and zero row and column sums → ξ has all coordinates positive and every row sum of Ghat G ξ is zero; reason: Ghat is symmetric by its defining formula, so column sums equal row sums; under the zero row sums of G this is equivalent to Gᵀξ=0 and imposes no reversibility or normalization
--   - encoding: every vertex error has norm tending to zero for any initial conditions → forward existence for every initial reference and network state, conjoined with vector convergence to zero for every global solution pair; reason: existence makes the initial-data clause explicit and prevents empty solution quantification; vector convergence in finite-dimensional real space is equivalent to the norm limit for each vertex
-- source:
--   Yu, Chen, Lü and Kurths, Synchronization via pinning control on general complex networks, SIAM J. Control Optim. 51(2) (2013), 1395–1416, https://doi.org/10.1137/100781699, p. 1402, Theorem 3.1 and (3.2), minimally corrected from (3.4) (PDF p. 8); (2.2)–(2.8), pp. 1397–1398 (PDF pp. 3–4); Definitions 2.3–2.4, p. 1399 (PDF p. 5); Lemma 2.12, p. 1401 (PDF p. 7)

import Mathlib
import Definitions.Def_PinningSync_Strong_Setting
import Definitions.Def_PinningSyncAudit_GeneralCoupling_correctedMatrix

namespace PinningSyncAudit.GeneralCoupling

open Matrix PinningSync.Strong

/-- Theorem 3.1, p. 1402 (PDF 8), corrected: full symmetric coupling term.
No symmetry or positivity of Γ, reversibility of G, or commutation is assumed.
The pinning vector generalizes the source's fraction-selected pins to any
nonnegative gains. Forward existence for every initial datum and convergence
of every global solution pair are both conclusions. -/
theorem theorem_3_1_corrected {N n : ℕ} (hN : 0 < N) (hn : 0 < n)
    (f : (Fin n → ℝ) → ℝ → (Fin n → ℝ))
    (hf : ContDiffOn ℝ 1 (fun p : (Fin n → ℝ) × ℝ => f p.1 p.2)
      (Set.univ ×ˢ Set.Ici 0))
    (K Γ : Matrix (Fin n) (Fin n) ℝ) (hA1 : Assumption1 f K Γ) (c : ℝ)
    (G : Matrix (Fin N) (Fin N) ℝ)
    (hG : IsCouplingMatrix G) (hsc : IsStronglyConnected G)
    (d : Fin N → ℝ) (hd : ∀ i, 0 ≤ d i)
    (ξ : Fin N → ℝ) (hξ : ∀ i, 0 < ξ i)
    (hΞ : ∀ i, ∑ j, Ghat G ξ i j = 0)
    (hlmi : (-(correctedMatrix K Γ c G ξ d)).PosDef) :
    (∀ (s₀ : Fin n → ℝ) (x₀ : Fin N → Fin n → ℝ),
      ∃ (s : ℝ → Fin n → ℝ) (x : ℝ → Fin N → Fin n → ℝ),
        s 0 = s₀ ∧ x 0 = x₀ ∧
          IsIsolatedSolution f s ∧ IsControlledSolution f c G Γ d s x) ∧
    (∀ (s : ℝ → Fin n → ℝ) (x : ℝ → Fin N → Fin n → ℝ),
      IsIsolatedSolution f s → IsControlledSolution f c G Γ d s x →
        GloballySynchronized s x) := by sorry

end PinningSyncAudit.GeneralCoupling
