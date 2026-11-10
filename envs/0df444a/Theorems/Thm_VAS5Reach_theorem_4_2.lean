-- Prove2me | Theorems.Thm_VAS5Reach_theorem_4_2
-- name    : VAS5Reach.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:29:51.809714+00:00
-- url     : https://prove2.me/theorems/a43e2d00-0406-49e9-8dd9-e7c5f21f2801
-- title:
--   Theorem 4.2 (generalized transformation area) — $C = (d+2)(B+1)^2\|T\|$ is a threshold, with runs inside $[\![V]\!]_{2B}$
-- statement:
--   Let $V$ be a $(d+2)$-VAS with transition set $T$, $I$ a set of two coordinates and $B \in \mathbb N$, and set
--   $$
--   C := (d + 2)(B + 1)^2 \|T\| .
--   $$
--   Then $\mathcal G_C$ is a generalized transformation area for $[\![V]\!]_{I,B}$. More precisely, for every $s, t \in \mathcal G_C$ and every $\mathbb Z$-run $s \xrightarrow{\pi}_{\mathbb Z} t$ in $[\![V]\!]_{I,B}$ there is a run $s \xrightarrow{\rho} t$ in $[\![V]\!]_{I,2B}$ with $\psi_\rho = \psi_\pi$, Parikh images counting the underlying transitions of $T$.
--
--   This supplies the polynomial thresholds used by every bound of Case II.
--
--   Differences from the source:
--   - generalization: [[V]]_B with I the first two coordinates (assumed w.l.o.g., p.16) → [[V]]_{I,B} for every set I of two coordinates; reason: renaming coordinates maps any pair to the first two, so the paper's case I = {1, 2} is an instance
--   - encoding: (d + 2)-VAS → VAS on a finite coordinate type ι with d + 2 = |ι|, so C = |ι|(B + 1)²‖T‖; reason: same constant
-- source:
--   Chen, Fu, Fu, Reachability in Five-Dimensional Vector Addition Systems Is PSPACE-Complete, arXiv:2610.40012 (held version, sha256 a74d76f9…), Theorem 4.2, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_VAS5Reach_vasSize
import Definitions.Def_VAS5Reach_VASS_IsRun
import Definitions.Def_VAS5Reach_encode
import Definitions.Def_VAS5Reach_IsTAThreshold

namespace VAS5Reach

/-- **Theorem 4.2 (Generalized Transformation Area Theorem).** Let `V` be a `(d + 2)`-VAS with
transition set `T` and let `B ∈ ℕ`. Set `C := (d + 2)(B + 1)² ∥T∥`. Then `G_C` is a generalized
transformation area. More precisely, for every `s, t ∈ G_C` and every `ℤ`-run `s −π→_Z t` in
`[[V]]_B`, there is a run `s −ρ→ t` in `[[V]]_{2B}` with `ψ_ρ = ψ_π`.

Source: W. Chen, B. Fu, Y. Fu, *Reachability in Five-Dimensional Vector Addition Systems Is
PSPACE-Complete*, arXiv:2610.40012 (held version, sha256 a74d76f9…), Theorem 4.2, printed p. 17 (PDF p. 19).

**Formalization Note** `d + 2 = Fintype.card ι`, so `C = card ι · (B + 1)² · ∥T∥`. The encoded
pair `I` is any two coordinates (the paper fixes the first two w.l.o.g.). Both clauses are
stated: `C` is a transformation-area threshold, and the run may be taken in `[[V]]_{2B}` (whose
states `((), u)`, `u ∈ [0, 2B]^I`, contain those of `[[V]]_B`). Parikh images count the
underlying VAS transitions. -/
theorem theorem_4_2 {ι : Type} [Fintype ι] (T : Finset (ι → ℤ)) (I : Finset ι) (B : ℕ)
    (hI : I.card = 2) :
    IsTAThreshold T I B (Fintype.card ι * (B + 1) ^ 2 * normT T) ∧
    ∀ s ∈ GC I B (Fintype.card ι * (B + 1) ^ 2 * normT T),
    ∀ t ∈ GC I B (Fintype.card ι * (B + 1) ^ 2 * normT T), ∀ π,
      (encode (VASS.ofVAS T) I B).IsZRun s.1 (fun j => (s.2 j : ℤ)) π t.1 (fun j => (t.2 j : ℤ)) →
      ∃ ρ, (encode (VASS.ofVAS T) I (2 * B)).IsRun s.1 s.2 ρ t.1 t.2 ∧
        parikh (ρ.map (underlying I)) = parikh (π.map (underlying I)) := by sorry

end VAS5Reach
