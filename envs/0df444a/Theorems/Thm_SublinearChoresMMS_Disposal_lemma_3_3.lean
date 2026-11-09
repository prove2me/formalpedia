-- Prove2me | Theorems.Thm_SublinearChoresMMS_Disposal_lemma_3_3
-- name    : SublinearChoresMMS.Disposal.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T03:35:23.182422+00:00
-- url     : https://prove2.me/theorems/c8b3cd7c-cbe0-45b8-a3b2-fb9536e274eb
-- title:
--   Lemma 3.3 — joint slot marginals and simultaneous rounding guarantees
-- statement:
--   Take the normalized positive distinct IDO regime and actual completed bundles from feasible representative packings. Let a realized coefficient vector satisfy the nonnegative simplex, capacity bounds, and reserved-agent cost equations. Form the corresponding complete fractional allocation $x$ and the general or custom slots of Section 3.3, using both cases $K\tau\le1$ and $K\tau>1$.
--
--   There is a finite law of assignments of real chores to owned slots with all of the following properties in every supported outcome:
--
--   1. Every chore goes to exactly one slot, each slot receives at most one real chore, each full slot receives a real chore, and assignments use positive slot fractions. Moreover, for every chore $e$ and slot $s$,
--
--   $$\Pr[A(e)=s]=x(e,s).$$
--
--   2. For each agent using general unit slots, the integral cost is at most $c_i(x_i)+\kappa_i$. Deleting the chore occupying her first slot, if any, leaves cost at most $c_i(x_i)$.
--
--   3. Every pure ordinary agent's integral bundle is MMS1, has cost at most $1+\kappa_i$, and has cost at most one after all $H$ chores are removed.
--
--   The same law provides all these guarantees. Slot witnesses are retained so that the first-slot and per-slot assertions are meaningful.
--
--   Differences from the source:
--   - generalization: q and the coefficient realization are chosen by the preceding coordination construction → any positive integer q<=n with padded m>=q divisible by q, any nonempty proper reserved set, any feasible representative packings, and any coefficient vector satisfying the deterministic coordination equations; reason: the slot argument requires only these constructed slots and equations, not the concentration parameters, segment count, or bound on mixed agents; every source realization is included
--   - encoding: a lottery over allocations with slot-assignment witnesses → a finite law on injective chore-to-owned-slot maps, with m+1 labels per agent including empty labels; reason: taking slot owners gives the complete allocation; unused labels have zero marginal, and per-slot equality and first-slot deletion retain all three bullets
--   - encoding: cost minimax share over labelled partitions → the negative of LittleCharity.MMS.mms evaluated at negative additive bundle costs; reason: negation exchanges finite maxima and minima; no goods nonnegativity predicate is imposed, and costShare_spec states the attained minimax characterization
-- source:
--   Zehan Lin, Xiaowei Wu, Shengwei Zhou, STOC 2027 submission #845 (October 2026), Lemma 3.3, §3.3 and equation (1), printed pp. 10–13 / PDF pp. 11–14; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/845.pdf

import Mathlib
import Definitions.Def_SublinearChoresMMS_Disposal_Slots

noncomputable section

namespace SublinearChoresMMS.Disposal

/-- Lemma 3.3, printed p. 12 / PDF p. 13. Integral outcomes retain their slot witnesses.
Both custom-slot cases and the general-slot first-slot removal are expressed. -/
theorem lemma_3_3 {n m q : ℕ} (hn : 0 < n) (hq : 0 < q) (hqn : q ≤ n)
    (hqm : q ≤ m) (hdiv : q ∣ m) (c : Cost n m) (hc : Normalized c)
    (R : Finset (Fin n)) (hR : 1 ≤ R.card) (hRn : R.card < n)
    (p : Packings n m q R) (hp : ∀ i, ValidPacking c i.val (p i))
    (v : Coefficients n q R) (hv : Coordinated c p v) :
    ∃ P : FiniteLaw (SlotAssignment n m),
      (∀ e s, P.mean (fun A => if A e = s then 1 else 0) = slotFraction c p v s e) ∧
      ∀ a : Fin P.size, 0 < P.weight a →
        Function.Injective (P.atom a) ∧
        (∀ e, 0 < slotFraction c p v (P.atom a e) e) ∧
        (∀ s, slotLoad (slotFraction c p v) s = 1 → ∃ e, P.atom a e = s) ∧
        (∀ i, GeneralAgent c p v i →
          cost c i (slotBundle (P.atom a) i) ≤ fractionalCost c i (realized c p v i) + kappa c i ∧
          cost c i (withoutFirst (P.atom a) i) ≤ fractionalCost c i (realized c p v i)) ∧
        ∀ i : Ordinary R, Pure v i →
          MMS1 c i.val (slotBundle (P.atom a) i.val) ∧
          cost c i.val (slotBundle (P.atom a) i.val) ≤ 1 + kappa c i.val ∧
          cost c i.val (slotBundle (P.atom a) i.val \ H p) ≤ 1 := by sorry

end SublinearChoresMMS.Disposal
