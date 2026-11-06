-- Prove2me | Theorems.Thm_TransvectionMixing_lemma_4_2_routed_paths_nonzero_minor
-- name    : TransvectionMixing.lemma_4_2_routed_paths_nonzero_minor
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:20:09.159129+00:00
-- url     : https://prove2.me/theorems/ebfba258-fc37-48bd-be29-93ce443e4fc2
-- title:
--   Lemma 4.2 — routed paths give a nonzero multiaffine minor of degree $\le T$
-- statement:
--   Fix a full-column-rank $X_0\in\mathbb F_q^{n\times k}$ and a skeleton $\sigma$ of length $T$. Let rows $b_1,\dots,b_k$ of $X_0$ be linearly independent, and suppose the time-expanded graph of $\sigma$ contains vertex-disjoint paths from $\{(b_i,0)\}$ to distinct final target rows $s_1,\dots,s_k$. With the coefficients $a_1,\dots,a_T$ as indeterminates and
--   $$
--   X_T=(I_n+a_TE_{J_T,I_T})\cdots(I_n+a_1E_{J_1,I_1})\,X_0 ,
--   $$
--   the minor $\det X_T[\{s_1,\dots,s_k\}]$ is a nonzero polynomial that is multiaffine (degree at most $1$ in each $a_t$) and has total degree at most $T$.
--
--   By Schwartz–Zippel this minor is nonzero at most coefficient vectors.
--
--   **Formalization Note** The minor's rows are taken in the order $s_1,\dots,s_k$, which changes only its sign.
--
--   Differences from the source:
--   - generalization: X₀ over 𝔽_q → X₀ over an arbitrary field; reason: the statement and its proof do not use finiteness of the field; 𝔽_q is an instance
--   - encoding: ℬ indexes k rows; distinct target rows s₁, …, s_k; det X_T[{s₁, …, s_k}] → injective b, s : Fin k → Fin n; the k × k submatrix on rows s (in that order) of coeffPoly σ · X₀; reason: row order only changes the sign
-- source:
--   Braverman, Jain, Newman, Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices over Large Fields (manuscript, sha256 217f833f…), Lemma 4.2, p.15

import Mathlib
import Definitions.Def_TransvectionMixing_walkMat
import Definitions.Def_TransvectionMixing_HasDisjointPaths

namespace TransvectionMixing

/-- **Lemma 4.2** (routed paths give a nonzero minor) (Braverman–Jain–Newman, *Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices over
Large Fields*, manuscript sha256 217f833f…, §4, p.15). Fix a full-column-rank
`X₀ ∈ 𝔽_q^{n×k}` and a skeleton `σ` of length `T`. Let `b₁, …, b_k` index `k` linearly
independent rows of `X₀`, and suppose the time-expanded graph contains vertex-disjoint paths
from `{(b, 0) : b ∈ ℬ}` to distinct final target rows `s₁, …, s_k`. Then, with the
coefficients `a₁, …, a_T` as indeterminates and `X_T = (Iₙ + a_T E_{J_T,I_T}) ⋯ X₀`,
`det X_T[{s₁, …, s_k}]` is a nonzero multiaffine polynomial of degree at most `T`.

**Formalization Note** The minor's rows are taken in the order `s₁, …, s_k`; reordering changes
only the sign. Multiaffine: every monomial has degree at most `1` in each variable. The field is
arbitrary. -/
theorem lemma_4_2_routed_paths_nonzero_minor (F : Type*) [Field F] (n k T : ℕ)
    (X0 : Matrix (Fin n) (Fin k) F) (hX0 : X0.rank = k) (σ : Skel n T)
    (b s : Fin k → Fin n) (hb : Function.Injective b) (hs : Function.Injective s)
    (hbind : LinearIndependent F (fun i => X0 (b i)))
    (P : Fin k → Fin (T + 1) → Fin n) (hP : ∀ i, IsRoutedPath σ (P i))
    (hP0 : ∀ i, P i 0 = b i) (hPT : ∀ i, P i (Fin.last T) ∈ Set.range s)
    (hdisj : ∀ u : Fin (T + 1), Function.Injective (fun i => P i u)) :
    (((coeffPoly (F := F) σ) * X0.map MvPolynomial.C).submatrix s id).det ≠ 0 ∧
      (∀ m ∈ (((coeffPoly (F := F) σ) * X0.map MvPolynomial.C).submatrix s id).det.support,
        ∀ v, m v ≤ 1) ∧
      (((coeffPoly (F := F) σ) * X0.map MvPolynomial.C).submatrix s id).det.totalDegree ≤ T := by sorry

end TransvectionMixing
