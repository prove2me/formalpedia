-- Prove2me | Theorems.Thm_SparseIncidenceHom_WidthComparison_decomposition_of_balanced_separators
-- name    : SparseIncidenceHom.WidthComparison.decomposition_of_balanced_separators
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:22:04.617741+00:00
-- url     : https://prove2.me/theorems/61a84d63-4f7f-4a0c-9e5a-7e322763d92b
-- title:
--   Lemma 3.6 — monotone subadditive separators yield a tree decomposition
-- statement:
--   Let $H$ be a finite covered hypergraph, $0<\eta<1$, and $r>0$. Let $f:2^{V(H)}\to\mathbb R_{\ge0}$ be monotone and subadditive, meaning $f(A\cup B)\le f(A)+f(B)$. Suppose that for every $X\subseteq V(H)$ there is a set $S\subseteq V(H)$ with $f(S)\le r$ such that every primal component $C$ after deleting $S$ satisfies
--   $$f(C\cap X)\le\eta f(X).$$
--   Then there is a tree decomposition $(T,B)$ of $H$ such that
--   $$f(B_t)\le\frac{2r}{1-\eta}+r\qquad(t\in V(T)).$$
--   The separator may depend on $X$. The conclusion holds for every bag of one decomposition. The set function need not be modular, submodular, normalized at the empty set, or a fractional-cover function. This is the general decomposition interface needed to turn separator cost bounds into width bounds.
--
--   Differences from the source:
--   - encoding: finite hypergraphs with the standing coverage and nonempty-edge conventions → Mathlib hypergraphs on an arbitrary finite carrier, with the full carrier as vertex set and explicit coverage and nonempty-edge fields; reason: every source hypergraph is represented by choosing its vertex set as carrier, including empty and disconnected induced hypergraphs
--   - encoding: a nonnegative real-valued set function and a finite nonempty decomposition tree → a real-valued set function with an explicit nonnegativity hypothesis and a tree on Fin(n+1) for an existential natural n; reason: these encode exactly all nonnegative functions and finite nonempty trees, with no normalization or size bound
-- source:
--   Matthias Lanzinger, STOC 2027 submission #662 (October 2026), p. 13, Lemma 3.6 ([Mar11, Section 5.2])

import Mathlib
import Definitions.Def_SparseIncidenceHom_WidthComparison_Separators

namespace SparseIncidenceHom.WidthComparison

theorem decomposition_of_balanced_separators {V : Type} [Fintype V]
    (H : FiniteHypergraph V) (η r : ℝ) (hη : 0 < η ∧ η < 1) (hr : 0 < r)
    (f : Set V → ℝ) (hf_nonneg : ∀ X, 0 ≤ f X)
    (hf_mono : Monotone f) (hf_subadd : ∀ A B, f (A ∪ B) ≤ f A + f B)
    (hsep : ∀ X : Set V, ∃ S : Set V, f S ≤ r ∧
      ∀ C : Set V, IsComponentAfter H S C → f (C ∩ X) ≤ η * f X) :
    ∃ (n : ℕ) (D : TreeDecomposition H n),
      ∀ t, f (D.bag t) ≤ 2 * r / (1 - η) + r := by sorry

end SparseIncidenceHom.WidthComparison
