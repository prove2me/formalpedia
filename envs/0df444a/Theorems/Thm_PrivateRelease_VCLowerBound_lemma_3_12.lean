-- Prove2me | Theorems.Thm_PrivateRelease_VCLowerBound_lemma_3_12
-- name    : PrivateRelease.VCLowerBound.lemma_3_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T16:07:34.41669+00:00
-- url     : https://prove2.me/theorems/1b26d3fa-9059-4a25-bac9-75553be92ffb
-- title:
--   Lemma 3.12 — $Q_T(T) - Q_T(T') = |T\Delta T'|/d$ for $T, T' \in \mathcal D_S$
-- statement:
--   Let $S$ be a finite set of $d = 2m$ universe elements and let $\mathcal D_S$ be the family of subsets of $S$ of size $m = d/2$. Let $T, T' \in \mathcal D_S$, and let $\varphi$ be a predicate that equals the indicator of $T$ on $S$ ($\varphi(x) = 1$ for $x \in T$, $\varphi(x) = 0$ for $x \in S \setminus T$); write $Q_T = Q_\varphi$. Evaluating the counting query on the databases $T$ and $T'$,
--
--   $$Q_T(T) - Q_T(T') = \frac{|T \,\Delta\, T'|}{d}.$$
--
--   The lemma converts query answers into symmetric-difference distances inside $\mathcal D_S$; it is what lets accurate answers to the queries $Q_{T'}$ identify the database.
--
--   **Formalization Note** The databases $T, T'$ are finite sets of distinct elements and $Q_\varphi(T) = |\{x \in T : \varphi(x) = 1\}|/|T|$. The identity needs only that $\varphi$ agrees with $\mathbf 1_T$ on $S$, not that $S$ is shattered. At $m = 0$ both sides are $0$.
-- source:
--   Blum, Ligett, Roth, A Learning Theory Approach to Non-Interactive Database Privacy, arXiv:1109.2229v1 (2011), p. 11, Lemma 3.12

import Mathlib
import Definitions.Def_PrivateRelease_VCLowerBound_Construction

namespace PrivateRelease.VCLowerBound

/-- Lemma 3.12 (p. 11). Let `S` be a finite set of `d = 2m` universe elements and `T, T′ ∈ D_S`
(subsets of `S` of size `m = d/2`), and let `φ` be any predicate equal to the indicator of `T` on `S`.
Then, with `Q_T = Q_φ` evaluated on the databases `T` and `T′`,
`Q_T(T) − Q_T(T′) = |T Δ T′| / d`. -/
theorem lemma_3_12 {X : Type} [DecidableEq X] (S : Finset X) (m : ℕ) (hS : S.card = 2 * m)
    (T T' : Finset X) (hT : T ∈ DS S m) (hT' : T' ∈ DS S m) (φ : X → Bool)
    (hφ : IsIndicatorOn S T φ) :
    countQF φ T - countQF φ T' = ((symmDiff T T').card : ℝ) / (S.card : ℝ) := by sorry

end PrivateRelease.VCLowerBound
