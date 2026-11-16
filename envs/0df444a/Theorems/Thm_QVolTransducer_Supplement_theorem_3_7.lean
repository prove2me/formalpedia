-- Prove2me | Theorems.Thm_QVolTransducer_Supplement_theorem_3_7
-- name    : QVolTransducer.Supplement.theorem_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:38:42.330214+00:00
-- url     : https://prove2.me/theorems/82ed92de-2043-499c-8c1a-c30e1c434122
-- title:
--   Theorem 3.7 — bounded mean estimation transducer BddMeanEst
-- statement:
--   Let $\pi$ be a probability distribution over a finite set $\Omega$ and $X:\Omega\to[0,1]$ with mean $\mu=\mathbb E_{\omega\sim\pi}[X(\omega)]\in(0,1)$; let $|\pi\rangle=\sum_\omega\sqrt{\pi(\omega)}|\omega\rangle$ and $|\bar\pi\rangle=\sum_\omega\sqrt{\pi(\omega)}\frac{\mu-X(\omega)}{\sqrt{\mu(1-\mu)}}|\omega\rangle$. Let $U$ be a bidirectional canonical transducer reflecting through $|\pi\rangle$, and $O_X$ one with uniform cost bound $C_X$ implementing $|\omega\rangle|0\rangle\rightsquigarrow|\omega\rangle(\sqrt{X(\omega)}|1\rangle+\sqrt{1-X(\omega)}|0\rangle)$. Let $t\ge1$ and $\epsilon\in(0,1)$. There are universal constants $c>0$, $k\in\mathbb N$ and a bidirectional canonical transducer $V=\mathtt{BddMeanEst}(X,U,t,\epsilon)$ with
--
--   $$|\pi\rangle|0\rangle\overset{V}{\rightsquigarrow}|\pi\rangle|\tilde\mu\rangle,\quad\text{complexity}\le c\,\big(C_X+W(U,|\pi\rangle)+W(U,|\bar\pi\rangle)\big)\cdot t\cdot\big(\log(2+t)\log(2+1/\epsilon)\big)^k,$$
--
--   such that the value $\tilde\mu$ obtained by measuring part of $|\tilde\mu\rangle$ in the computational basis satisfies
--
--   $$|\mathbb E[\tilde\mu]-\mu|\le\epsilon,\qquad \mathrm{Var}[\tilde\mu]\le\frac{91\mu}{t^2}+\epsilon.$$
--
--   This ports the unbiased, non-destructive bounded mean estimator of Cornelissen and Hamoudi to transducers; the state $|\pi\rangle$ is restored.
--
--   **Formalization Note** $|\tilde\mu\rangle$ is a state of an output register (answer and garbage) initialised to $|0\rangle$; $V$, the register and the readout are chosen before the input.
--
--   Differences from the source:
--   - encoding: states, oracles and constants depend on an implicit input x ∈ D (p.14); the canonical transducers do not → an explicit input type D with oracles O x, data as functions of x, and ∃ transducer before ∀ x; reason: the convention of p.14 made explicit; same instances
--   - encoding: Hilbert spaces V, H, W of the transducers → coordinate spaces ℂ^V over finite types; reason: Part I's transducers are finite-dimensional (pp.4, 36); the published base items use the same model
--   - generalization: a uniform cost bound C_X (one number) → C_X may depend on the input x; reason: the proof composes the bounds input by input; a constant bound is the special case
--   - encoding: a state |µ̃⟩ of which a subset of the qubits is measured → |π⟩ ⊗ φ_x with φ_x on an output register Fin (a+1) × Fin (g+1) starting in |0⟩, a readout val fixed before x, and E, Var, probabilities given by the published readMean, readVar, readProb; reason: the published reading of Theorems 10.2–10.3 (answer and garbage registers)
--   - reading: Õ(·) / O(· polylog) → universal c > 0 and k ∈ ℕ with a factor (log(2+t)·log(2+1/ϵ))^k; reason: §2.1's Õ with log(2+·) so the factors are ≥ log 2 > 0 for every parameter value (base decisions 3–4)
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Theorem 3.7, p.25 (PDF p.27)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_mm_basic
import Definitions.Def_QVolTransducer_BiCanonical
import Definitions.Def_QVolTransducer_starState
import Definitions.Def_QVolTransducer_readMean
import Definitions.Def_QVolTransducer_Supplement_perpVec

namespace QVolTransducer.Supplement

open QAlgorithms

/-- **Bounded mean estimation transducer** (Cornelissen, Apers, Gribling, *Improved quantum volume
estimation with transducers and amortized quantum walks*, arXiv:2609.40217 (version of November 3,
2026, sha256 40d7b52d…), Theorem 3.7, p.25 (PDF p.27)).

There are universal constants `c > 0` and `k ∈ ℕ` with the following property. Let `π` be a
probability distribution over a finite set `Ω`, `X : Ω → [0, 1]` with mean `µ = E_{ω∼π}[X(ω)]`,
`0 < µ < 1`, `|π⟩ = Σ_ω √π(ω)|ω⟩` and `|π̄⟩ = Σ_ω √π(ω)(µ − X(ω))/√(µ(1 − µ))|ω⟩`. Let `U` be a
bidirectional canonical transducer that reflects through `|π⟩` and `O_X` one with uniform cost
bound `C_X` that implements `|ω⟩|0⟩ ⇝ |ω⟩(√X(ω)|1⟩ + √(1 − X(ω))|0⟩)`. Let `t ≥ 1` and
`ϵ ∈ (0, 1)`. Then there is a bidirectional canonical transducer `V = BddMeanEst(X, U, t, ϵ)`
mapping `|π⟩|0⟩ ⇝ |π⟩|µ̃⟩` with complexity at most
`c (C_X + W(U,|π⟩) + W(U,|π̄⟩)) · t · (log(2+t) log(2+1/ϵ))^k`, such that the value `µ̃` read out by
measuring part of `|µ̃⟩` in the computational basis satisfies `|E[µ̃] − µ| ≤ ϵ` and
`Var[µ̃] ≤ 91µ/t² + ϵ`.

**Formalization Note** The implicit input (p.14) is explicit (`D`, `O_x`, `π_x`, `X_x`, `C_X(x)`);
`V`, its output register and its readout are chosen before `x`. `|µ̃⟩` is a state `φ_x` of an output
register `Fin (a+1) × Fin (g+1)` (answer and garbage, "measuring a subset of the qubits") starting in
`|0⟩ = |(0,0)⟩`; `µ̃ = val(i)` for the measured answer `i`, and `E`, `Var` are the published
`readMean`, `readVar`. `O(·polylog(t, 1/ϵ))` is read as universal `c`, `k` with `log(2+·)` factors
(the reading of the published Theorem 10.2). -/
theorem theorem_3_7 :
    ∃ c : ℝ, 0 < c ∧ ∃ k : ℕ,
      ∀ (Ω Q Wu Wx : Type) [Fintype Ω] [DecidableEq Ω] [Fintype Q] [DecidableEq Q]
        [Fintype Wu] [DecidableEq Wu] [Fintype Wx] [DecidableEq Wx]
        (D : Type) (O : D → Matrix.unitaryGroup Q ℂ) (π X : D → Ω → ℝ) (CX : D → ℝ)
        (U : BiCanonical Ω Q Wu) (OX : BiCanonical (Ω × Fin 2) Q Wx),
        (∀ x, MarkovMixing.IsDist (π x)) → (∀ x ω, X x ω ∈ Set.Icc (0 : ℝ) 1) →
        (∀ x, 0 < finMean (π x) (X x)) → (∀ x, finMean (π x) (X x) < 1) →
        IsReflectionThrough U O (fun x => sqrtVec (π x)) →
        (∀ x (ψ : EuclideanSpace ℂ (Ω × Fin 2)),
          transductionComplexity (OX.apply (O x)) ψ ≤ CX x * ‖ψ‖ ^ 2) →
        (∀ x ω, Transduces (OX.apply (O x)) (ket (ω, (0 : Fin 2)))
          (tensorVec (ket ω) (coinVec (X x ω)))) →
        ∀ t ϵ : ℝ, 1 ≤ t → 0 < ϵ → ϵ < 1 →
        ∃ (a g n : ℕ) (V : BiCanonical (Ω × (Fin (a + 1) × Fin (g + 1))) Q (Fin n))
          (val : Fin (a + 1) → ℝ), ∀ x,
          ∃ (φ : EuclideanSpace ℂ (Fin (a + 1) × Fin (g + 1)))
            (w : EuclideanSpace ℂ ((Q ⊕ Q) × Fin n)),
            TransducesWith (V.apply (O x)) (tensorVec (sqrtVec (π x)) (ket (0, 0)))
              (tensorVec (sqrtVec (π x)) φ) w ∧
            ‖w‖ ^ 2 ≤ c * (CX x + transductionComplexity (U.apply (O x)) (sqrtVec (π x)) +
                transductionComplexity (U.apply (O x)) (perpVec (π x) (X x))) *
              t * (Real.log (2 + t) * Real.log (2 + 1 / ϵ)) ^ k ∧
            |readMean φ val - finMean (π x) (X x)| ≤ ϵ ∧
            readVar φ val ≤ 91 * finMean (π x) (X x) / t ^ 2 + ϵ := by sorry

end QVolTransducer.Supplement
