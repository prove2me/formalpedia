-- Prove2me | Theorems.Thm_Supermodularity_Monotonicity_argmax_mono_of_strictly_increasing_differences
-- name    : Supermodularity.Monotonicity.argmax_mono_of_strictly_increasing_differences
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T05:28:32.478243+00:00
-- url     : https://prove2.me/theorems/6e32d387-9dbd-4f42-959b-ad3cb8cb890a
-- title:
--   Theorem 2.8.4 - optimal solutions across parameters are ordered under strictly increasing differences
-- statement:
--   Let $X$, $T$, $S_t$, and $f(x,t)$ be as in `argmax_increasing_of_increasing_differences`
--   (so $t \mapsto S_t$ is increasing in the induced set order and $f(x,t)$ is supermodular in
--   $x$ for each $t$), except that $f(x,t)$ is now assumed to have **strictly** increasing
--   differences in $(x,t)$ on $X \times T$ (see `StrictlyIncreasingDifferencesOn`). If $t'
--   \prec t''$ in $T$, $x' \in \operatorname{argmax}_{x \in S_{t'}} f(x,t')$, and $x'' \in
--   \operatorname{argmax}_{x \in S_{t''}} f(x,t'')$, then $x' \preceq x''$.
--
--   This is the pairwise content of Theorem 2.8.4: strengthening increasing differences to
--   *strictly* increasing differences upgrades the conclusion of Theorem 2.8.1 from "the two
--   argmax sets are related by $\sqsubseteq$" to the stronger statement that *every* optimal
--   solution at the larger parameter value dominates *every* optimal solution at the smaller
--   one — a genuine strengthening, since $\sqsubseteq$ alone would only force this for the
--   least and greatest elements of each set. Consequently, any selection $x(t)$ of one
--   optimal solution per parameter value is automatically increasing in $t$, with no need to
--   consistently pick, say, the greatest element of each argmax set.
--
--   **Formalization Note** The book states this result together with the immediate corollary
--   that any selection function $t \mapsto x(t)$ with $x(t) \in \operatorname{argmax}_{x \in
--   S_t} f(x,t)$ is increasing on $\{t : \operatorname{argmax}_{x\in S_t}f(x,t) \ne
--   \emptyset\}$; that corollary is a direct restatement of the pairwise claim proved here
--   (apply it to $x(t')$ and $x(t'')$) and is not stated as a separate conjunct.
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 2011, p. 78, Theorem 2.8.4

import Mathlib
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Definitions.Def_Supermodularity_Monotonicity_StrictlyIncreasingDifferencesOn

namespace Supermodularity.Monotonicity

theorem argmax_mono_of_strictly_increasing_differences {X T : Type*} [Lattice X]
    [PartialOrder T] (S : T → Set X) (f : X → T → ℝ)
    (hS : ∀ ⦃t t' : T⦄, t ≤ t' → Supermodularity.Lattices.InducedSetOrder (S t) (S t'))
    (hsuper : ∀ t : T, SupermodularOn (fun x => f x t) Set.univ)
    (hdiff : StrictlyIncreasingDifferencesOn f Set.univ)
    {t' t'' : T} (ht : t' < t'') {x' x'' : X}
    (hx' : x' ∈ S t' ∧ ∀ y ∈ S t', f y t' ≤ f x' t')
    (hx'' : x'' ∈ S t'' ∧ ∀ y ∈ S t'', f y t'' ≤ f x'' t'') :
    x' ≤ x'' := by sorry

end Supermodularity.Monotonicity
