-- Prove2me | Theorems.Thm_QuantumOnePCA369_PauliPCA_lepskii_estimate
-- name    : QuantumOnePCA369.PauliPCA.lepskii_estimate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:37:47.623044+00:00
-- url     : https://prove2.me/theorems/43ef6fe5-2949-468d-aeb5-78044ba4cb24
-- title:
--   Lemma 3.2 — Lepskii's method estimates a matrix mean in operator norm
-- statement:
--   Let $X_0,X_1,\dots$ be an i.i.d. sequence of $d\times d$ Hermitian random matrices with $\|\mathbb E X_j^2\|_\infty\le\beta^2$, and let $\beta^2_{\max}\ge8\beta^2_{\min}>0$, $M\ge1$, $d\ge1$. There are universal constants $C,a$ such that Algorithm 1, run with an arbitrary exact eigensolver, satisfies:
--
--   1. it reads only the first $(I+1)M$ samples, $I=\lceil\log_2(\beta^2_{\max}/\beta^2_{\min})\rceil$, and $(I+1)M\le C\,M\log(\beta^2_{\max}/\beta^2_{\min})$;
--   2. its running time is at most $C\,M\,d^{\,a}\log(\beta^2_{\max}/\beta^2_{\min})^2$ on every input;
--   3. if $\beta^2_{\min}\le\beta^2\le\beta^2_{\max}$, then for every $\delta>0$, with probability at least $1-\delta$,
--   $$\|\hat X-\mathbb EX_j\|_\infty\le C\sqrt{\frac{\beta^2\log\!\big(\beta^2_{\max}/\beta^2_{\min}\cdot d/\delta\big)}{M}}.$$
--
--   This is the operator-norm mean estimator applied to the per-round tomography estimates in Lemma 3.7; it adapts to the unknown second moment $\beta^2$ within the window $[\beta^2_{\min},\beta^2_{\max}]$.
--
--   Running time is the tick count of the program in the unit-cost real RAM of §2 (p. 5): one tick per real or complex arithmetic operation, square root, logarithm, ceiling, comparison, array read or write and loop step, $n$ ticks per measured copy, and one call of an exact eigensolver on a $d'\times d'$ Hermitian matrix charged $d'^3+1$. The cubic charge is a chosen polynomial envelope for this idealized primitive, not a bit-complexity or numerical-stability claim.
--
--   **Formalization Note** The random matrices are measurable, mutually independent, identically distributed and Hermitian, with integrable entries of $X_j$ and $X_j^2$, on an arbitrary probability space; expectations are entrywise integrals. The failure event has (outer) probability at most $\delta$, which is vacuous for $\delta\ge1$.
--
--   Differences from the source:
--   - encoding: an i.i.d. sequence {X_j} of Hermitian matrices with ‖E X_j²‖_∞ ≤ β² → X : ℕ → Ω → matrices on a probability space, iIndepFun, identically distributed with X_0, measurable, Hermitian for every ω, entries of X_0 and X_0² integrable; reason: makes E X_j and E X_j² meaningful (an integral of a non-integrable function is 0 in Lean); finite second moment is the source's hypothesis
--   - encoding: uses O(M log(β²max/β²min)) examples → the output is unchanged when samples with index ≥ (I+1)M change, and (I+1)M ≤ C·M·log(β²max/β²min); reason: states both which samples are read and the O-bound on their number
--   - encoding: O(M poly(d) log(β²max/β²min)²) time → cost ≤ C·M·d^a·log(β²max/β²min)² with universal C, a; reason: poly(d) with d ≥ 1 is dominated by a power of d
--   - encoding: running time in the real RAM model with spectral computations' numerical details omitted (p. 5) → tick count of the defined program: one tick per scalar operation, comparison, array access and loop step, n ticks per measured copy, an exact eigensolver charged d'^3 + 1; reason: §2 defers spectral computations to the real RAM model; the cubic charge is a polynomial envelope and the paper's bounds only use poly(d')
--   - encoding: eigenvectors of a degenerate or zero matrix chosen arbitrarily (p. 15) → the statement holds for every SpectralChooser (any exact eigensolver returning a sorted orthonormal eigenbasis of each Hermitian input); reason: quantifying over all choosers is the source's 'arbitrary' choice
--   - reading: Algorithms 1 and 3 use δ (lines 5, 7) without listing it as an input → δ is an explicit input; Algorithm 3 passes δ/2^ℓ to each Algorithm 1 call and Algorithm 4 passes δ/n to each layer; reason: these are the union bounds of the proofs of Lemmas 3.7 (p. 11) and 4.3 (p. 17)
--   - encoding: with probability at least 1 − δ → the failure event has outer measure at most δ, for every δ > 0; reason: the strong form of the source's claim; vacuous for δ ≥ 1
--   - encoding: dimension d and block size M → 1 ≤ d and 1 ≤ M; reason: a dimension and a block size are positive; at M = 0 the averages are undefined
--   - encoding: ≲ and O(·) → one pair of universal constants C, a quantified before all data; reason: the source's constants are absolute
-- source:
--   Dutch Hansen, Jerry Li, Quantum 1-PCA with Pauli Measurements in Nearly Linear Time, STOC 2027 submission #369 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/369.pdf, p. 7, Lemma 3.2 (proof pp. 7–8); Algorithm 1, p. 7

import Mathlib
import Definitions.Def_QuantumOnePCA369_PauliPCA_Basic
import Definitions.Def_QuantumOnePCA369_PauliPCA_Lepskii

open MeasureTheory ProbabilityTheory

namespace QuantumOnePCA369.PauliPCA

theorem lepskii_estimate :
    ∃ C a : ℝ, 0 < C ∧
      ∀ (ch : SpectralChooser) (d M : ℕ) (βmin2 βmax2 : ℝ),
        1 ≤ d → 1 ≤ M → 0 < βmin2 → 8 * βmin2 ≤ βmax2 →
        -- examples: only the first `(I+1)M` samples are read, and `(I+1)M = O(M log(β²max/β²min))`
        ((∀ (δ : ℝ) (X X' : ℕ → Matrix (Fin d) (Fin d) ℂ),
            (∀ j < (lepskiiI βmin2 βmax2 + 1) * M, X j = X' j) →
              (lepskii ch d M βmin2 βmax2 δ X).val = (lepskii ch d M βmin2 βmax2 δ X').val) ∧
          (((lepskiiI βmin2 βmax2 + 1) * M : ℕ) : ℝ) ≤ C * M * Real.log (βmax2 / βmin2)) ∧
        -- time: `O(M poly(d) log(β²max/β²min)²)` for every input
        (∀ (δ : ℝ) (X : ℕ → Matrix (Fin d) (Fin d) ℂ),
          ((lepskii ch d M βmin2 βmax2 δ X).cost : ℝ) ≤
            C * M * (d : ℝ) ^ a * Real.log (βmax2 / βmin2) ^ 2) ∧
        -- accuracy for an i.i.d. sequence of Hermitian matrices with `‖𝔼 X_j²‖_∞ ≤ β²`
        (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
            (X : ℕ → Ω → Fin d → Fin d → ℂ) (β2 δ : ℝ),
          iIndepFun X P → (∀ j, IdentDistrib (X j) (X 0) P P) → (∀ j, Measurable (X j)) →
          (∀ j ω, (Matrix.of (X j ω)).IsHermitian) →
          (∀ a b, Integrable (fun ω => X 0 ω a b) P) →
          (∀ a b, Integrable (fun ω => (Matrix.of (X 0 ω) * Matrix.of (X 0 ω)) a b) P) →
          opNorm (Matrix.of fun a b => ∫ ω, (Matrix.of (X 0 ω) * Matrix.of (X 0 ω)) a b ∂P) ≤ β2 →
          βmin2 ≤ β2 → β2 ≤ βmax2 → 0 < δ →
          P {ω | ¬ opNorm ((lepskii ch d M βmin2 βmax2 δ (fun j => Matrix.of (X j ω))).val -
                Matrix.of (fun a b => ∫ ω', X 0 ω' a b ∂P)) ≤
              C * Real.sqrt (β2 * Real.log (βmax2 / βmin2 * d / δ) / M)} ≤ ENNReal.ofReal δ) := by sorry

end QuantumOnePCA369.PauliPCA
