-- Prove2me | Theorems.Thm_QStateSearch_entropy_step
-- name    : QStateSearch.entropy_step
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:15:30.448303+00:00
-- url     : https://prove2.me/theorems/4b1ff21d-fdc8-4cf1-8288-b1502327e3d8
-- title:
--   Proof of Lemma 3 — one prover message raises $\mathbb E\ln(1/\mu(C))$ by at most $b\ln2$
-- statement:
--   Let $\mu$ be a finite measure, $C$ a measurable set with $\mu(C)>0$, and $f$ a measurable map into $\{0,\dots,2^b-1\}$ (the reply of a padded $b$-bit prover message), so that the sets $C_z=C\cap f^{-1}(z)$ partition $C$. Put $p_z=\mu(C_z)/\mu(C)$. Then
--   $$
--   \sum_z p_z\ln\frac1{\mu(C_z)}=\ln\frac1{\mu(C)}+\sum_z p_z\ln\frac1{p_z}\le\ln\frac1{\mu(C)}+b\ln2 .
--   $$
--
--   With $\mu=\mu_D$, $C=C(h)$ and $C_z=C(hz)$, this is the step of the proof of Lemma 3 that charges each prover message at most its length in bits: the expected logarithmic inverse mass of the compatible set grows by the entropy of the reply, which is at most $\ln 2^b$.
--
--   **Formalization Note** Terms with $p_z=0$ are $0$ on both sides.
--
--   Differences from the source:
--   - generalization: the Haar measure $\mu_D$, the compatible set $C(h)$ and the cells $C(hz)$ → any finite measure $\mu$, any measurable $C$ with $\mu(C)>0$, the cells of any measurable reply map $f$; reason: the paper's case is $\mu=\mu_D$, $C=C(h)$, $f(\psi)=P_\psi(h)$
--   - encoding: a $b$-bit reply $z$ → $z\in\{0,\dots,2^b-1\}$; masses as real numbers; reason: same objects
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), proof of Lemma 3, display after the definition of $p(z\mid h)$, p.12

import Mathlib
open MeasureTheory

namespace QStateSearch

/-- **Proof of Lemma 3, one-message entropy step.** A padded `b`-bit prover message, given by a
measurable reply map `f` into `Fin (2 ^ b)`, partitions the compatible set `C` into the cells
`C_z = C ∩ f⁻¹{z}`. With `p_z = μ(C_z)/μ(C)`,
`∑_z p_z ln(1/μ(C_z)) = ln(1/μ(C)) + ∑_z p_z ln(1/p_z) ≤ ln(1/μ(C)) + b ln 2`.

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), proof of Lemma 3, display after "Let p(z | h) = μ_D(C(hz))/μ_D(C(h))", p.12.

**Formalization Note.** Stated for any finite measure `μ` (the paper's is the Haar measure
`μ_D`) and measurable `C` of positive mass. Masses are `(μ X).toReal`. Lean's `log 0 = 0` is
harmless: every logarithm of a null cell is multiplied by `p_z = 0`. -/
theorem entropy_step {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (C : Set α) (hC : MeasurableSet C) (hpos : 0 < μ C) (b : ℕ) (f : α → Fin (2 ^ b))
    (hf : ∀ z, MeasurableSet (f ⁻¹' {z})) :
    ∑ z, ((μ (C ∩ f ⁻¹' {z})).toReal / (μ C).toReal) * Real.log (1 / (μ (C ∩ f ⁻¹' {z})).toReal)
        = Real.log (1 / (μ C).toReal) +
          ∑ z, ((μ (C ∩ f ⁻¹' {z})).toReal / (μ C).toReal) *
            Real.log (1 / ((μ (C ∩ f ⁻¹' {z})).toReal / (μ C).toReal)) ∧
    ∑ z, ((μ (C ∩ f ⁻¹' {z})).toReal / (μ C).toReal) * Real.log (1 / (μ (C ∩ f ⁻¹' {z})).toReal)
        ≤ Real.log (1 / (μ C).toReal) + b * Real.log 2 := by sorry

end QStateSearch
