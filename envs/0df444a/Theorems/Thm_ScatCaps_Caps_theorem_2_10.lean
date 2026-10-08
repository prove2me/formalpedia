-- Prove2me | Theorems.Thm_ScatCaps_Caps_theorem_2_10
-- name    : ScatCaps.Caps.theorem_2_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:06:03.456741+00:00
-- url     : https://prove2.me/theorems/76717fc6-d265-4067-a76a-8ea27a343600
-- title:
--   Theorem 2.10, p. 16 — L_U = {⟨x² + b x^{2^{2n+1}} + xω⟩ : x ∈ 𝔽*_{2^{3n}}} is a scattered 𝔽₂-linear set of PG(2, 2^{2n}) of rank 3n
-- statement:
--   Let $n > 1$, let $E = \mathbb F_{2^{6n}}$, viewed as a 3-dimensional vector space over $\mathbb F_{2^{2n}}$ so that $PG(E, \mathbb F_{2^{2n}}) = PG(2, 2^{2n})$, and let $\omega \in \mathbb F_{2^{2n}} \setminus \mathbb F_{2^n}$. Let $b \in \mathbb F^*_{2^{3n}}$ with $N_{2^{3n}/2^n}(b) \ne 1$ and such that
--
--   $$x + b\,x^{2^{2n+1} - 1} \notin \mathbb F_{2^n} \quad \text{for each } x \in \mathbb F^*_{2^{3n}} .$$
--
--   Then, with $U = \{x^2 + b x^{2^{2n+1}} + x\omega : x \in \mathbb F_{2^{3n}}\}$, the set
--
--   $$L_U = \{\langle x^2 + b x^{2^{2n+1}} + x\omega\rangle_{\mathbb F_{2^{2n}}} : x \in \mathbb F^*_{2^{3n}}\}$$
--
--   is a scattered $\mathbb F_2$-linear set of $PG(2, 2^{2n})$ of rank $3n$: $U$ is an $\mathbb F_2$-subspace with $|U| = 2^{3n}$, and scattered with respect to $\mathbb F_{2^{2n}}$.
--
--   With Proposition 2.9 it gives, for $q = 2^t$, $t = 2n \ge 4$, the maximum scattered linear set of $PG(2, q)$ that Proposition 4.7 needs.
--
--   **Formalization Note** $\omega$ is the standing element of $\mathbb F_{2^{2n}} \setminus \mathbb F_{2^n}$ fixed on p. 4; the statement holds for every such $\omega$. The norm condition is kept as printed although the scattered-ness argument does not use it. The characteristic-2 instance follows from $|E| = 2^{6n}$ and is stated explicitly.
-- source:
--   Bartoli, Giulietti, Marino & Polverino, Maximum scattered linear sets and complete caps in Galois spaces, arXiv:1512.07467v1, p. 16, Theorem 2.10 (setting of §2, p. 4)

import Mathlib
import Definitions.Def_ScatCaps_LinearSets_Model

namespace ScatCaps.Caps

theorem theorem_2_10 (E : Type*) [Field E] [Fintype E] [CharP E 2] (n : ℕ) (hn : 1 < n)
    (hE : Fintype.card E = 2 ^ (6 * n))
    (ω : E) (hω : ω ∈ ScatCaps.LinearSets.subfieldOf E 2 1 (2 * n)) (hω' : ω ∉ ScatCaps.LinearSets.subfieldOf E 2 1 n)
    (b : E) (hb : b ∈ ScatCaps.LinearSets.subfieldOf E 2 1 (3 * n)) (hb0 : b ≠ 0)
    (hbN : ScatCaps.LinearSets.relNorm 2 (3 * n) n b ≠ 1)
    (hbx : ∀ x ∈ ScatCaps.LinearSets.subfieldOf E 2 1 (3 * n), x ≠ 0 →
      x + b * x ^ (2 ^ (2 * n + 1) - 1) ∉ ScatCaps.LinearSets.subfieldOf E 2 1 n) :
    ScatCaps.LinearSets.IsFqSubspace (⊥ : Subfield E) (ScatCaps.LinearSets.sec2Set (ScatCaps.LinearSets.subfieldOf E 2 1 (3 * n)) (ScatCaps.LinearSets.binom 2 n 1 1 b) ω) ∧
      ScatCaps.LinearSets.HasRank (⊥ : Subfield E) (ScatCaps.LinearSets.sec2Set (ScatCaps.LinearSets.subfieldOf E 2 1 (3 * n)) (ScatCaps.LinearSets.binom 2 n 1 1 b) ω) (3 * n) ∧
      ScatCaps.LinearSets.IsScattered (⊥ : Subfield E) (ScatCaps.LinearSets.subfieldOf E 2 1 (2 * n))
        (ScatCaps.LinearSets.sec2Set (ScatCaps.LinearSets.subfieldOf E 2 1 (3 * n)) (ScatCaps.LinearSets.binom 2 n 1 1 b) ω) := by sorry

end ScatCaps.Caps
