-- Prove2me | Theorems.Thm_TriFormQ_lemma_10
-- name    : TriFormQ.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:58:15.945632+00:00
-- url     : https://prove2.me/theorems/afd353bc-82c4-4e0b-82c6-bf83519e8f87
-- title:
--   Lemma 10: in a random $d$-dimensional affine subspace with projected weights, $\tilde Y_H/\tilde X_H\ge Y_H/\tilde X_H\ge 3/68$ with probability $\ge 11/104$
-- statement:
--   Let $f$ be a trilinear form on $\mathbb F_q^n$ and let $d,e$ be integers with $d<n$, $d-\mathrm{AR}(f)\ge 4$ and $e-\mathrm{AR}(f)\ge 4$. Let $H$ be a uniformly random affine subspace of $\mathbb F_q^n$ of dimension $d$, and independently let $w_1,\dots,w_e$ be uniform in $\mathbb F_q^n$, defining the projection $\Pi$ of Eq. (15). Let $X_H,Y_H$ and $\tilde X_H,\tilde Y_H$ be the total and good weights with the original and the projected weights. Then the event
--
--   $$Y_H\ \ge\ \tfrac12\,\mathbb E[Y_H]\quad\text{and}\quad \tilde X_H\ \le\ 8\,\mathbb E[\tilde X_H]$$
--
--   has probability at least $11/104$, and for every outcome in this event
--
--   $$\frac{\tilde Y_H}{\tilde X_H}\ \ge\ \frac{Y_H}{\tilde X_H}\ \ge\ \frac{3}{68}.$$
--
--   Expectations and probabilities are over both $H$ and $\Pi$. Consequently, sampling a point of $H$ with probability proportional to the projected weights returns a good base point with constant probability, which is the core of Theorem 6.
--
--   **Formalization Note** The sample space is the product of the set of $d$-dimensional affine subspaces and the set of $e$-tuples of probe vectors, with the uniform distribution; probabilities are counting ratios and expectations are averages.
--
--   Differences from the source:
--   - reading: a random affine $d$-dimensional subspace → uniform over the nonempty affine subspaces of dimension exactly $d$; reason: Lemma 6's "uniformly random affine d-dimensional subspace"; the construction $v_0+\mathrm{span}\{v_1,\dots,v_d\}$ of §5.2.1 can have smaller dimension, where Lemma 6's inclusion probabilities fail
--   - reading: conditioned on this event, (23) holds → (23) holds for every outcome in the event; reason: (23) is a pointwise consequence on the event in the paper's proof
--   - encoding: probabilities and expectations over $H$ and $\Pi$ → counting ratios and averages over the finite uniform product sample space; reason: finite uniform spaces; $\mathbb E[Y_H]$ is averaged over $H$ only, which equals its average over the product
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), Lemma 10, Eqs. (22)–(23), p.27 (PDF p.30)

import Definitions.Def_TriFormQ_AR
import Definitions.Def_TriFormQ_affSubspaces
import Definitions.Def_TriFormQ_YH
import Definitions.Def_TriFormQ_XtH
import Definitions.Def_TriFormQ_YtH

namespace TriFormQ

open Classical in
/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), Lemma 10, Eqs. (22)–(23), p.27
(PDF p.30): "Let d < n, and suppose d − AR(f) ≥ 4 and e − AR(f) ≥ 4. Let H be a random affine
d-dimensional subspace in V, and choose Π independently as in Eq. (15). Then, with probability
at least 11/104, Y_H ≥ ½ E[Y_H] and X̃_H ≤ 8 E[X̃_H]. (22) Conditioned on this event,
Ỹ_H/X̃_H ≥ Y_H/X̃_H ≥ 3/68. (23) Here expectations and probabilities are over both H and Π; for
X_H and Y_H, only the randomness of H matters."

**Formalization Note.** The sample space is `Ω = 𝓗 × (Fin e → 𝔽ⁿ)` with the uniform
distribution, where `𝓗 = affSubspaces F n d` is the set of nonempty affine subspaces of
dimension exactly `d` (Lemma 6's "uniformly random affine d-dimensional subspace") and the
second factor lists the `e` independent uniform probe vectors `w₁, …, w_e` of Eq. (15).
Probabilities are counting ratios over `Ω`, expectations are averages (`E[Y_H]` over `𝓗`, which
equals its average over `Ω`). "Conditioned on this event" is read as: for every outcome in the
event. -/
theorem lemma_10 {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ} (θ : TriForm F n)
    (d e : ℕ) (hdn : d < n) (hd : 4 ≤ (d : ℝ) - AR θ) (he : 4 ≤ (e : ℝ) - AR θ) :
    let 𝓗 := affSubspaces F n d
    let Ω := 𝓗 ×ˢ (Finset.univ : Finset (Fin e → Vec F n))
    let EY := (∑ H ∈ 𝓗, YH θ H) / 𝓗.card
    let EXt := (∑ ω ∈ Ω, XtH θ ω.2 ω.1) / Ω.card
    let E := Ω.filter fun ω => EY / 2 ≤ YH θ ω.1 ∧ XtH θ ω.2 ω.1 ≤ 8 * EXt
    (11 / 104 : ℝ) ≤ (E.card : ℝ) / Ω.card ∧
      ∀ ω ∈ E, YH θ ω.1 / XtH θ ω.2 ω.1 ≤ YtH θ ω.2 ω.1 / XtH θ ω.2 ω.1 ∧
        (3 / 68 : ℝ) ≤ YH θ ω.1 / XtH θ ω.2 ω.1 := by sorry

end TriFormQ
