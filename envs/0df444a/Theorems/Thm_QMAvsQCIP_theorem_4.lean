-- Prove2me | Theorems.Thm_QMAvsQCIP_theorem_4
-- name    : QMAvsQCIP.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:49:24.816855+00:00
-- url     : https://prove2.me/theorems/c345370e-911e-43da-972f-0d260412b370
-- title:
--   Theorem 4 — independent-marking incompressibility: $\Pr[\exists m:\mathrm{Dec}(m,R)\in\binom{A_O}{t}]\le2^s\delta^t$
-- statement:
--   Let $X$ be a finite set, $0<\delta<1$, and integers $s\ge0$ and $1\le t\le|X|$. Sample $O(z)\leftarrow\mathrm{Bernoulli}(\delta)$ independently for $z\in X$, write $A_O=\{z\in X:O(z)=1\}$, and independently sample a shared random tape $R$. Let $\mathrm{Enc}(O,R)\in\{0,1\}^s$ be an arbitrary encoder and $\mathrm{Dec}(m,R)$ a decoder without oracle access. Then
--   $$
--   \Pr_{O,R}\Big[\mathrm{Dec}(\mathrm{Enc}(O,R),R)\in\binom{A_O}{t}\Big]\le\Pr_{O,R}\Big[\exists m\in\{0,1\}^s:\ \mathrm{Dec}(m,R)\in\binom{A_O}{t}\Big]\le2^s\delta^t. \tag{10}
--   $$
--   The left side is the success probability of the experiment $\mathrm{Expt}_{\mathrm{Mark}}$: the decoder outputs $t$ distinct marked elements.
--
--   This is the bound for independently marked inputs that, with the parameters of Eq. (7), gives the second half of Corollary 2.
--
--   **Formalization Note** "$T\in\binom{A_O}{t}$" is $T\subseteq A_O$ and $|T|=t$. The tape is a probability space; the decoder's output events are measurable; the encoder is arbitrary (if its event is not measurable, the measure of it is the outer measure, and the first inequality still holds).
--
--   Differences from the source:
--   - encoding: shared random tape $R$ of unrestricted classical algorithms → a probability space $(\Omega,\mu)$ with decoder outputs measurable in the tape; probabilities over $(O,R)$ as $\sum_O\Pr[O]\,\mu\{\ldots\}$; reason: standing convention that an algorithm's output is a random variable of its tape
--   - encoding: unrestricted encoder $\mathrm{Enc}$ → an arbitrary function of the sample and the tape, with no measurability; the first event is then measured by the outer measure; reason: outer measure is monotone, so the first inequality holds as stated, and it is the measure itself for every measurable (algorithmic) encoder
-- source:
--   Cakan, Separating QMA from QCIP with a Classical Oracle, arXiv:2610.03648 (held version, sha256 687668af…34ec), Theorem 4, Eq. (10), p.20

import Definitions.Def_QMAvsQCIP_bernExp

set_option autoImplicit false

namespace QMAvsQCIP

open MeasureTheory

/-- **Theorem 4 (Independent-marking incompressibility).** Let `X` be finite, `0 < δ < 1`,
`s ≥ 0` and `1 ≤ t ≤ |X|`. Mark each `z ∈ X` independently with probability `δ`
(`O(z) ← Bernoulli(δ)`, `A_O = {z : O(z) = 1}`) and independently sample a shared random tape `R`
from a probability space `(Ω, μ)`. For every encoder `Enc(O, R) ∈ {0,1}^s` and every decoder
`Dec(m, R)` with no oracle access (outputs measurable in the tape),
`Pr[Dec(Enc(O,R), R) ∈ (A_O choose t)] ≤ Pr[∃ m ∈ {0,1}^s : Dec(m, R) ∈ (A_O choose t)] ≤ 2^s δ^t`.

Cakan, *Separating QMA from QCIP with a Classical Oracle*, arXiv:2610.03648 (held version,
sha256 687668af…34ec), Theorem 4, p.20 (PDF p.23).

**Formalization Note.** ExptMark outputs `1` iff `T = Dec(m, R)` consists of `t` distinct marked
elements, i.e. `T ⊆ A_O` and `|T| = t`. Probabilities over `(O, R)` are
`∑_O Pr[O] · μ{ω | …}`. The encoder is arbitrary; if its event is not measurable, `μ` of it is
the outer measure, and the first inequality still holds. -/
theorem theorem_4 (X : Type) [Fintype X] [DecidableEq X] (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (s t : ℕ) (ht1 : 1 ≤ t) (htX : t ≤ Fintype.card X)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Enc : (X → Bool) → Ω → (Fin s → Bool)) (Dec : (Fin s → Bool) → Ω → Finset X)
    (hDec : ∀ m T, MeasurableSet {ω | Dec m ω = T}) :
    bernExp δ (fun O => (μ {ω | Dec (Enc O ω) ω ⊆ Finset.univ.filter (fun z => O z = true) ∧
        (Dec (Enc O ω) ω).card = t}).toReal) ≤
      bernExp δ (fun O => (μ {ω | ∃ m, Dec m ω ⊆ Finset.univ.filter (fun z => O z = true) ∧
        (Dec m ω).card = t}).toReal) ∧
    bernExp δ (fun O => (μ {ω | ∃ m, Dec m ω ⊆ Finset.univ.filter (fun z => O z = true) ∧
        (Dec m ω).card = t}).toReal) ≤ 2 ^ s * δ ^ t := by sorry

end QMAvsQCIP
