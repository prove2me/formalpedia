-- Prove2me | Theorems.Thm_ScatPoly_Construction_semilinear_L_M
-- name    : ScatPoly.Construction.semilinear_L_M
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:16:44.020027+00:00
-- url     : https://prove2.me/theorems/6e2affa6-f084-4273-a3a0-a0b97158a809
-- title:
--   §3, p. 7 — L and M are 𝔽_{q^t}-semilinear with companion automorphisms x ↦ x^q and x ↦ x^{q^{t−1}}
-- statement:
--   Let $q = p^r$ be an odd prime power, $t \ge 3$, $n = 2t$, $F = \mathbb F_{q^n}$, $\mathbb F_{q^t} \subseteq F$ the subfield of order $q^t$, and $h \in F$ with $h^{q^t+1} = -1$. Let
--   $$L(x) = x^q - h^{1-q^{t+1}} x^{q^{t+1}}, \qquad M(x) = x^{q^{t-1}} + h^{1-q^{2t-1}} x^{q^{2t-1}}.$$
--   Then $L$ and $M$ are additive, and for every $\lambda \in \mathbb F_{q^t}$ and $x \in F$
--   $$L(\lambda x) = \lambda^q L(x), \qquad M(\lambda x) = \lambda^{q^{t-1}} M(x).$$
--   That is, $L$ and $M$ are $\mathbb F_{q^t}$-semilinear maps of $F$ with companion automorphisms $x \mapsto x^q$ and $x \mapsto x^{q^{t-1}}$.
--
--   Semilinearity is what makes the kernels and images of $L$ and $M$ into $\mathbb F_{q^t}$-subspaces.
--
--   **Formalization Note.** The hypotheses are §3's standing ones (Theorem 3.1's range $n = 2t$, $t \ge 3$, $q$ odd, $h^{q^t+1} = -1$); the semilinearity itself uses only the characteristic. $\mathbb F_{q^t}$ is the fixed field of $x \mapsto x^{q^t}$ (`subfieldOf F p r t`).
-- source:
--   Longobardi, Marino, Trombetti & Zhou, A large family of maximum scattered linear sets of PG(1, q^n) and their associated MRD codes, arXiv:2102.08287v3, p. 7, §3, the sentence after display (3)

import Mathlib
import Definitions.Def_ScatCaps_LinearSets_Model
import Definitions.Def_ScatPoly_Construction_Model

namespace ScatPoly.Construction

open ScatCaps.LinearSets in
theorem semilinear_L_M (F : Type*) [Field F] [Fintype F] (p r t q : ℕ) [Fact p.Prime] [CharP F p]
    (hp : Odd p) (hr : 0 < r) (hq : q = p ^ r) (ht : 3 ≤ t)
    (hcard : Fintype.card F = q ^ (2 * t))
    (h : F) (hh : h ^ (q ^ t + 1) = -1) :
    (∀ x y : F, Lmap q t h (x + y) = Lmap q t h x + Lmap q t h y) ∧
    (∀ x y : F, Mmap q t h (x + y) = Mmap q t h x + Mmap q t h y) ∧
    (∀ l ∈ subfieldOf F p r t, ∀ x : F, Lmap q t h (l * x) = l ^ q * Lmap q t h x) ∧
    (∀ l ∈ subfieldOf F p r t, ∀ x : F,
      Mmap q t h (l * x) = l ^ q ^ (t - 1) * Mmap q t h x) := by sorry

end ScatPoly.Construction
