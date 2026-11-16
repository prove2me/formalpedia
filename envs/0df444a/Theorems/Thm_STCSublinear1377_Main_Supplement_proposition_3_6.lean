-- Prove2me | Theorems.Thm_STCSublinear1377_Main_Supplement_proposition_3_6
-- name    : STCSublinear1377.Main.Supplement.proposition_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:24:58.62721+00:00
-- url     : https://prove2.me/theorems/fb410bf5-db50-4ad3-a44f-c87414689439
-- title:
--   Proposition 3.6 — Heavy set with small boundary avoiding a root
-- statement:
--   Let $Q$ be a connected undirected graph on $N$ vertices with nonnegative integer edge capacities (zero capacities allowed on edges of the connected support graph) and a distinguished vertex $o$. Let $\nu$ be a nonnegative integer vertex weight with $\nu(o)=0$, $W=\nu(V_Q)$, and let $\ell$ be an integer with $1\le\ell\le W$. There is an absolute constant $C>0$ such that for every $r>0$ some randomized algorithm, running in time polynomial in the input length (vertex weights written in unary, so polynomial in $N+W$ and the capacity bits), always outputs a set $A\subseteq V_Q\setminus\{o\}$, and with probability at least $1-(N+W)^{-r}$
--
--   $$\nu(A)\ge\ell,\qquad b_Q(A)\le C\log^{3/2}(N+W)\cdot\min\{b_Q(C'): o\notin C',\ \nu(C')\ge\ell\}.$$
--
--   The set $A$ may be disconnected and its weight may exceed $\ell$. The proposition is the search step of the swap procedure in Theorem 3.5.
--
--   Differences from the source:
--   - generalization: ν polynomially bounded, polynomial running time → ν arbitrary, read in unary; running time polynomial in the input length (N + W and the capacity bits); reason: for polynomially bounded ν the unary encoding has length polynomial in N, so the source statement is the special case
--   - reading: β = O(log^{3/2}(N + W)); a randomized algorithm finds A → one absolute C chosen before the confidence r and the input; every tape outputs A ⊆ V_Q ∖ {o}; with probability ≥ 1 − (N + W)^{−r} both conclusions hold; reason: the approximation factor does not depend on the confidence; high probability is obtained by independent repetitions keeping a quota-feasible set of least boundary, as on p.13
-- source:
--   Sunny Atalig, Marek Chrobak, Petr Kolman, Hans Raj Tiwary, Sublinear Approximations for Spanning Tree Congestion, STOC 2027 submission #1377 (October 2026), pinned submission, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1377.pdf, Proposition 3.6, PDF/printed p.11; reduction in Appendix A.4, p.18

import Definitions.Def_STCSublinear1377_Main_Supplement_Quota
set_option autoImplicit false

namespace STCSublinear1377.Main.Supplement

/-- Proposition 3.6: zero capacities on a connected support graph, `ν(o) = 0`, `1 ≤ ℓ ≤ W`; the
output may be disconnected and need only reach the quota. Vertex weights are read in unary. -/
theorem proposition_3_6 :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → ∃ a : RandomDataMachine,
      ∀ n : ℕ, ∀ f : WeightedGraph n,
        f.vertices = Finset.univ → f.wellFormed → f.integral → f.connected →
        ∀ o : Fin n, ∀ ν : Fin n → ℕ, ν o = 0 →
        ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ ∑ v, ν v →
        let W : ℝ := ((∑ v, ν v : ℕ) : ℝ)
        let input := integerGraphBits f ++ natBits o.val ++ unaryWeights ν ++ natBits ℓ
        (∀ tape : Fin (a.tapeLength input) → Bool,
          ∃ A : Finset (Fin n), a.output input tape = setBits A ∧ o ∉ A) ∧
        dataProbability a input (fun out => ∃ A : Finset (Fin n),
          out = setBits A ∧ o ∉ A ∧ ℓ ≤ ∑ v ∈ A, ν v ∧
          f.boundary A ≤ C * Real.rpow (Real.log ((n : ℝ) + W)) (3 / 2 : ℝ) *
            quotaOpt f o ν ℓ) ≥
          1 - Real.rpow ((n : ℝ) + W) (-r) := by sorry

end STCSublinear1377.Main.Supplement
