-- Prove2me | Theorems.Thm_SpecExtremalConj_lemma_3_5
-- name    : SpecExtremalConj.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:12:33.856585+00:00
-- url     : https://prove2.me/theorems/7c3289b7-9070-4538-a677-379dda76128d
-- title:
--   Lemma 3.5: $e(G[V_i\setminus L])\le a$ and a large independent set
-- statement:
--   Throughout, $r\ge2$ and $F$ is a finite graph such that, for every $n\ge n_1$, every graph of $\mathrm{Ex}(n,F)$ is a relabelled $T_{n,r}$ plus exactly $a$ edges (the standing assumption of Section 3). "$G$" denotes any $F$-free graph on $n$ vertices of maximum spectral radius ($G\in\mathrm{Ex}_{sp}(n,F)$). A partition $V(G)=V_1\cup\dots\cup V_r$ is called **maximizing** if $\sum_{i<j}e(V_i,V_j)$ is maximum over all partitions into $r$ parts. Let $L$ be the low-degree set (6) for $\epsilon$.
--
--   There is $\epsilon_0>0$ such that for every $\epsilon\in(0,\epsilon_0)$ there is $n_0$ such that for every $n\ge n_0$, every $G\in\mathrm{Ex}_{sp}(n,F)$, every maximizing partition and every $i\in[r]$:
--
--   1. $e(G[V_i\setminus L])\le a$;
--   2. there is an independent set $I_i\subseteq V_i\setminus L$ with
--   $$|I_i|\ \ge\ |V_i|-\epsilon^{1/3}n-a.$$
--
--   Differences from the source:
--   - reading: ǫ sufficiently small (the ǫ of Lemma 3.4, with some θ < 1/(100r⁵ℓ), 2ǫ < θ³, ℓ ≫ max{a, |V(F)|}) → ∃ ε₀ > 0, ∀ ε ∈ (0, ε₀), ∃ n₀, ∀ n ≥ n₀; reason: θ and ℓ do not occur in the conclusion; every ε below θ₀³/2 admits a θ as in Lemma 3.4
--   - reading: §3 standing assumption: the graphs in Ex(n, F) are obtained from T_{n,r} by adding a edges (n large) → IsTuranPlusConst F r a n₁: for every n ≥ n₁, every member of Ex(n, F) contains a relabelled spanning T_{n,r} and has e(T_{n,r}) + a edges; reason: the paper uses the assumption only at large orders; a threshold n₁ is the weaker hypothesis, hence the stronger statement
--   - generalization: the partition V_1 ∪ … ∪ V_r fixed in Lemma 3.3 (one maximizing partition) → every maximizing partition P : Fin n → Fin r (IsMaxCut G P); reason: the proofs use only maximality of Σ e(V_i, V_j); a maximizing partition exists because there are finitely many, so the statement specializes to the paper's
--   - encoding: "obtained from T_{n,r} by adding edges" → contains a relabelled spanning copy of turanGraph n r (ContainsSpanningTuran), with the number of added edges read off the edge count; reason: graphs are taken up to isomorphism; a graph contains a spanning T_{n,r} with k further edges exactly when it is T_{n,r} plus k edges
--   - encoding: an n-vertex graph → a simple graph on Fin n; reason: the spectral radius, F-freeness and edge counts are invariant under relabelling, so every n-vertex graph is an instance
--   - encoding: λ(G), the largest eigenvalue of A(G) → specRad G, the supremum of the eigenvalues of the real symmetric matrix G.adjMatrix ℝ; reason: the supremum of the (finitely many, real) eigenvalues is the largest one; same value on every graph
-- source:
--   Wang, Kang, Xue, On a conjecture of spectral extremal problems, arXiv:2203.10831v1, Lemma 3.5, p. 8

import Mathlib
import Definitions.Def_SpecExtremalConj_IsSpecExtremal
import Definitions.Def_SpecExtremalConj_IsTuranPlusConst
import Definitions.Def_SpecExtremalConj_IsMaxCut
import Definitions.Def_SpecExtremalConj_part
import Definitions.Def_SpecExtremalConj_edgesIn
import Definitions.Def_SpecExtremalConj_lowDegSet
open Finset SimpleGraph

namespace SpecExtremalConj

/-- **Lemma 3.5 (few edges inside V_i \ L; a large independent set).** Wang, Kang, Xue, *On a conjecture of spectral extremal problems*, arXiv:2203.10831v1, Lemma 3.5, p. 8:
"For each i ∈ [r], e(G[Vi \ L]) ≤ a. Furthermore, for each i ∈ [r], there exists an independent
set Ii ⊆ Vi \ L such that |Ii| ≥ |Vi| − ǫ^{1/3}n − a."

**Standing hypotheses (§3, p. 4).** `r ≥ 2` (Theorem 1.2) and `IsTuranPlusConst F r a n₁`: for
every `n ≥ n₁`, every graph of Ex(n, F) is a relabelled T_{n,r} plus exactly `a` edges. "G" is
any spectral extremal graph (`IsSpecExtremal F G`) on `Fin n`, n large.

There is `ε₀ > 0` such that for every `ε ∈ (0, ε₀)` there is `n₀` such that for `n ≥ n₀`, every
spectral extremal `G` on `Fin n`, every maximizing partition `P` and every part `V_i`:
`e(G[V_i \ L]) ≤ a`, and some independent set `I_i ⊆ V_i \ L` has
`|I_i| ≥ |V_i| − ε^{1/3} n − a`, where `L = lowDegSet G r ε` is (6).

**Formalization Note.** The paper's ǫ is that of Lemma 3.4 (sufficiently small, with some θ
satisfying θ < 1/(100r⁵ℓ) and 2ǫ < θ³); since θ does not occur in the conclusion, this is the
threshold `ε₀`. "The partition" is any maximizing partition `P : Fin n → Fin r` (`IsMaxCut G P`); the paper fixes
one (Lemma 3.3), its proofs use only maximality, so quantifying over all of them is a
generalization. -/
theorem lemma_3_5 {W : Type*} [Fintype W] (F : SimpleGraph W) (r a n₁ : ℕ) (hr : 2 ≤ r)
    (hF : IsTuranPlusConst F r a n₁) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        IsSpecExtremal F G → ∀ P : Fin n → Fin r, IsMaxCut G P → ∀ i : Fin r,
          edgesIn G (part P i \ lowDegSet G r ε) ≤ a ∧
          ∃ I ⊆ part P i \ lowDegSet G r ε, G.IsIndepSet (I : Set (Fin n)) ∧
            (#(part P i) : ℝ) - ε ^ ((1 : ℝ) / 3) * n - a ≤ #I := by sorry

end SpecExtremalConj
