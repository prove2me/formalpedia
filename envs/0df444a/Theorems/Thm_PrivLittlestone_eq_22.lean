-- Prove2me | Theorems.Thm_PrivLittlestone_eq_22
-- name    : PrivLittlestone.eq_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:39:09.657294+00:00
-- url     : https://prove2.me/theorems/f45fb725-71bd-40ea-9275-ef854de3ab7e
-- title:
--   Eq. (22) — counts $|T_s(V)| \le [2(d+1)]^{d-s}$ and $|T_s(V) \cap W_h| \le [2(d+1)]^{r-s}$ [MY26, Lemma 11]
-- statement:
--   Fix a nonempty class $H$ with $\mathrm{LDim}(H) = d \ge 1$ and a public witness assignment as in Lemma A.1. For every nonempty version space $V = V_v(S)$:
--   $$
--   |T_s(V)| \le [2(d+1)]^{d-s} \quad (0 \le s \le d), \qquad |T_s(V) \cap W_h| \le [2(d+1)]^{r-s} \quad (\rho(h) = r,\ 0 \le s \le r). \tag{22}
--   $$
--
--   The local bound, with exponent equal to a rank difference, is what gives the fibre axiom of the Littlestone candidate system; a bound on $|C(S)|$ alone would not.
--
--   **Formalization Note** Imported: the paper cites [MY26, Lemma 11] and does not prove (22). Cardinalities are extended natural numbers, so the bounds include finiteness.
--
--   Differences from the source:
--
--   - encoding: cardinalities |·| → Set.encard in ℕ ∪ {∞}; reason: an infinite set has cardinality ∞, so the bounds also assert finiteness, as the paper's counts do
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Appendix A.2.2, (22), p.18 (citing [MY26, Lemma 11])

import Mathlib
import Definitions.Def_PrivLittlestone_IsWitnessAssignment
import Definitions.Def_PrivLittlestone_versionCell
import Definitions.Def_PrivLittlestone_selT

namespace PrivLittlestone

/-- **Exact counts (22) ([MY26], Lemma 11)** (He–He, *Private Online Learning of Littlestone
Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562), Appendix
A.2.2, (22), p.18). Fix a nonempty class `H` with `LDim(H) = d ≥ 1` and a public witness
assignment as in Lemma A.1. For every nonempty version space `V = V_v(S)`:
1. `|T_s(V)| ≤ [2(d + 1)]^{d−s}` for `0 ≤ s ≤ d`;
2. `|T_s(V) ∩ W_h| ≤ [2(d + 1)]^{r−s}` for every `h ∈ U` of rank `ρ(h) = r` and `0 ≤ s ≤ r`.

**Formalization Note** Imported: the paper cites [MY26, Lemma 11] and does not prove (22).
Cardinalities are `Set.encard` (an infinite set has cardinality `⊤`, so the bounds include
finiteness). -/
theorem eq_22 {X : Type*} (H : Set (X → Bool)) (d : ℕ) (hH : H.Nonempty)
    (hd : UnderstandingML.ldim H = d) (hd1 : 1 ≤ d) (Aw : (X → Bool) → Finset X)
    (hAw : IsWitnessAssignment H d Aw) (S : List (X × Bool)) (v : Fin S.length → Bool)
    (hV : (versionCell H d S v).Nonempty) :
    (∀ s : ℕ, s ≤ d →
      (selT H d Aw (versionCell H d S v) s).encard ≤ (((2 * (d + 1)) ^ (d - s) : ℕ) : ℕ∞)) ∧
    (∀ h ∈ localUniverse H d, ∀ s : ℕ, s ≤ rankOf H d h →
      (selT H d Aw (versionCell H d S v) s ∩ witnessSpace H d Aw h).encard ≤
        (((2 * (d + 1)) ^ (rankOf H d h - s) : ℕ) : ℕ∞)) := by sorry

end PrivLittlestone
