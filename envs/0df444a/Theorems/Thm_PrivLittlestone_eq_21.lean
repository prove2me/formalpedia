-- Prove2me | Theorems.Thm_PrivLittlestone_eq_21
-- name    : PrivLittlestone.eq_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:39:32.598996+00:00
-- url     : https://prove2.me/theorems/3bcf9660-0256-4a5d-bfdb-7fd301dbeb23
-- title:
--   Eq. (21) — coverage: every $h \in V$ lies in $W_g$ for some selected $g \in D(V)$ of rank $\ge \rho(h)$
-- statement:
--   Fix a nonempty class $H$ with $\mathrm{LDim}(H) = d \ge 1$ and a public witness assignment as in Lemma A.1. For every sample $S$ and label vector $v$ with nonempty version space $V = V_v(S)$, and every $h \in V$, some $g \in D(V)$ satisfies
--   $$
--   h \in W_g, \qquad \rho(g) \ge \rho(h), \qquad \rho(g) > \rho(h) \text{ if } h \notin D(V). \tag{21}
--   $$
--
--   Since $g, h \in V$, they agree on every sample instance; this gives coverage of the Littlestone candidate system even on unrealizable samples.
--
--   Differences from the source: none.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Appendix A.2.2, (21), p.18

import Mathlib
import Definitions.Def_PrivLittlestone_IsWitnessAssignment
import Definitions.Def_PrivLittlestone_versionCell
import Definitions.Def_PrivLittlestone_selD

namespace PrivLittlestone

/-- **Coverage (21) ([MY26], Lemma 10)** (He–He, *Private Online Learning of Littlestone Classes
and Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562), Appendix A.2.2,
(21), p.18). Fix a nonempty class `H` with `LDim(H) = d ≥ 1` and a public witness assignment as
in Lemma A.1. For every sample `S`, every label vector `v` with nonempty version space
`V = V_v(S)`, and every `h ∈ V`, some `g ∈ D(V)` satisfies `h ∈ W_g`, `ρ(g) ≥ ρ(h)`, and
`ρ(g) > ρ(h)` if `h ∉ D(V)`. -/
theorem eq_21 {X : Type*} (H : Set (X → Bool)) (d : ℕ) (hH : H.Nonempty)
    (hd : UnderstandingML.ldim H = d) (hd1 : 1 ≤ d) (Aw : (X → Bool) → Finset X)
    (hAw : IsWitnessAssignment H d Aw) (S : List (X × Bool)) (v : Fin S.length → Bool)
    (hV : (versionCell H d S v).Nonempty) :
    ∀ h ∈ versionCell H d S v, ∃ g ∈ selD H d Aw (versionCell H d S v),
      h ∈ witnessSpace H d Aw g ∧ rankOf H d h ≤ rankOf H d g ∧
        (h ∉ selD H d Aw (versionCell H d S v) → rankOf H d h < rankOf H d g) := by sorry

end PrivLittlestone
