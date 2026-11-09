-- Prove2me | Theorems.Thm_PulseSyncLowerBound_Pulse_lemma_12
-- name    : PulseSyncLowerBound.Pulse.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:00:53.250435+00:00
-- url     : https://prove2.me/theorems/58d23410-ea5a-4d82-ba97-7e305ae9d752
-- title:
--   Lemma 12 — prefix and suffix maps
-- statement:
--   For a protocol $\mathcal A$ and natural horizon $T$, let $X=R(T,2)$ and $Y=R(T+1,1)$. The actual prefix $P$ and suffix $S$ satisfy all three assertions:
--
--   1. Both maps are chromatic simplicial maps from $Y$ to $X$.
--   2. For every vertex $y$ of $Y$,
--   $$\operatorname{out}(Sy)=\operatorname{out}(y).$$
--   3. For every crash-free trace $\rho_0,\ldots,\rho_{T+1}$,
--   $$P\rho_{T+1}=\rho_T,$$
--   and $S\rho_1,\ldots,S\rho_{T+1}$ is a crash-free trace starting at $\mu(\rho_1)$.
--
--   These are statements about the recursively computed maps and reachable views, with no simpliciality or output preservation built into their definitions.
--
--   Differences from the source:
--   - encoding: processes numbered 1 through n with pairwise disjoint finite local state sets (operationally nonempty) → Fin n identities and arbitrary finite nonempty dependent local state types, with identity-tagged states and views; reason: zero-based relabelling and tagged disjoint union preserve every process, state, and execution; nonemptiness is the operational state convention used explicitly in the Lemma 12 proof
--   - encoding: maps on the actual vertex set V(X) → maps on ambient tagged views constrained only when their singleton or edge is a face; reason: any map on actual vertices extends arbitrarily to the unused ambient views; no unreachable view is made a vertex
--   - generalization: Section 6 fixes a non-trivial counting protocol and T=floor(f/2) → any finite-state protocol, arbitrary output type and any natural T; reason: the conclusions use only the operational definitions; specializing to counting outputs and T=floor(f/2) gives every source clause
--   - encoding: finite configuration sequence through T+1 → a sequence indexed on natural times, constrained and observed only through T+1; reason: later entries are unused and can always be supplied arbitrarily, so this represents exactly the finite traces
-- source:
--   Joel Rybicki, STOC 2027 submission #508 (October 2026), pinned published-basis artifact; Lemma 12; PDF p.20 / printed p.18; papers/stoc2027-508/source.pdf; SHA-256 5237f877941c17d0913977954f4f4b6ccba70f65ceae5dc47f15029dbd68765f.

import Definitions.Def_PulseSyncLowerBound_Pulse_Views

namespace PulseSyncLowerBound.Pulse

attribute [local instance] Classical.propDecidable Classical.decEq

theorem lemma_12 {n : ℕ} {O : Type} (P : Protocol n O) (T : ℕ) :
    (IsSimplicial (RoundComplex P (T + 1) 1) (RoundComplex P T 2) (viewPrefix P T) ∧
      IsSimplicial (RoundComplex P (T + 1) 1) (RoundComplex P T 2) (viewSuffix P T) ∧
      (∀ y : TaggedView P (T + 1), {y} ∈ RoundComplex P (T + 1) 1 →
        (viewPrefix P T y).1 = y.1 ∧ (viewSuffix P T y).1 = y.1)) ∧
    (∀ y : TaggedView P (T + 1), {y} ∈ RoundComplex P (T + 1) 1 →
      viewOutput P T (viewSuffix P T y) = viewOutput P (T + 1) y) ∧
    (∀ a : (r : ℕ) → ViewConfig P r, CrashFreeTrace P (T + 1) a →
      prefixConfig P T (a (T + 1)) = a T ∧
      CrashFreeTrace P T (fun r => suffixConfig P r (a (r + 1))) ∧
      suffixConfig P 0 (a 1) = stateConfig P 1 (a 1)) := by sorry

end PulseSyncLowerBound.Pulse
