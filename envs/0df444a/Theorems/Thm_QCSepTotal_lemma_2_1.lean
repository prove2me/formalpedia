-- Prove2me | Theorems.Thm_QCSepTotal_lemma_2_1
-- name    : QCSepTotal.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:33:40.707324+00:00
-- url     : https://prove2.me/theorems/80c42700-e63f-4672-919f-812ca1234b40
-- title:
--   Lemma 2.1 — prediction from total variation: $\Delta(Z^B,Z\otimes U_1)>\delta$ gives error $<1/2-\delta$
-- statement:
--   Let $B$ be a binary random variable and $Z$ a random variable on a common probability space, and let $\delta>0$. If
--   $$\Delta\bigl(Z^B,\ Z\otimes U_1\bigr)>\delta ,$$
--   where $Z^B$ is the joint law of $(Z,B)$ and $U_1$ the uniform distribution on $\{0,1\}$, then $B$ can be predicted from $Z$ with error less than $1/2-\delta$: there is a function $\varphi$ with $\Pr[\varphi(Z)\neq B]<1/2-\delta$.
--
--   It rules out "easy" input distributions in the proof of Theorem 4.1 (the case where (7) fails).
--
--   **Formalization Note** The probability space is discrete, given by a probability mass function.
--
--   Differences from the source:
--   - generalization: a finite probability space → any discrete probability space (a PMF on any type); reason: finite spaces are a special case
--   - reading: Z^B (superscript notation) → the joint law of (Z, B); reason: the proof on p.3 expands Δ(Z^B, Z ⊗ U₁) as the distance between the joint law and the product
--   - encoding: U₁ uniform on F₂ → uniform on Bool; reason: same two-point uniform law
-- source:
--   Le Gall, Improved Separations between Quantum and Classical Communication Complexity of Total Functions, arXiv:2609.16726 (held version, sha256 970e1476…), Lemma 2.1, p.3

import Mathlib
import Definitions.Def_QCSepTotal_tv

namespace QCSepTotal

/-- **Lemma 2.1** (Prediction and total variation; F. Le Gall, *Improved Separations between Quantum and Classical Communication Complexity of Total Functions*, arXiv:2609.16726 (held version, sha256 970e1476…), p.3). Let `B` be a
binary random variable and `Z` a random variable. If `Δ(Z^B, Z ⊗ U₁) > δ` for some `δ > 0`,
then `B` can be predicted from `Z` with error less than `1/2 − δ`: there is a prediction rule
`φ` with `Pr[φ(Z) ≠ B] < 1/2 − δ`.

**Formalization Note.** `Z^B` is the joint law of `(Z, B)` (the proof, p.3, expands it as such);
`U₁` is the uniform law on `Bool`. The random variables live on a discrete probability space
`(Ω, P)` with `P` a `PMF`, of which the paper's finite spaces are a special case. -/
theorem lemma_2_1 {Ω α : Type*} (P : PMF Ω) (B : Ω → Bool) (Z : Ω → α) (δ : ℝ) (hδ : 0 < δ)
    (h : δ < tv (P.map fun ω => (Z ω, B ω)) (prodLaw (P.map Z) (PMF.uniformOfFintype Bool))) :
    ∃ φ : α → Bool, prob P {ω | φ (Z ω) ≠ B ω} < 1 / 2 - δ := by sorry

end QCSepTotal
