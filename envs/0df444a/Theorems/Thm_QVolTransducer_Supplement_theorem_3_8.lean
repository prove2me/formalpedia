-- Prove2me | Theorems.Thm_QVolTransducer_Supplement_theorem_3_8
-- name    : QVolTransducer.Supplement.theorem_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:39:38.82963+00:00
-- url     : https://prove2.me/theorems/e4de5e83-1d7d-4bd1-a597-727a181bf671
-- title:
--   Theorem 3.8 — quantile estimator QuantileEst
-- statement:
--   Let $\pi$ be a probability distribution over a finite set $\Omega$, $X:\Omega\to[0,M]$ with $M>0$, and $Q_X(p):=\inf\{t\in[0,M]:\mathbb P_{x\sim\pi}[X(x)\le t]\ge p\}$. Let $p\in(0,1)$, $\epsilon\in(0,\min\{p,1-p\})$ and $\Delta>0$ with $Q_X(p+\epsilon)-Q_X(p-\epsilon)\ge\Delta$, and $\rho>0$. Let $U$ reflect through $|\pi\rangle$, and for every $t\in[0,M]$ let $O_X^{(t)}$ be a bidirectional canonical transducer with uniform cost bound $C_X$ acting as $|\omega\rangle|0\rangle\rightsquigarrow|\omega\rangle(\sqrt{X_t(\omega)}|1\rangle+\sqrt{1-X_t(\omega)}|0\rangle)$, where $X_t:=\tfrac14+\tfrac12\mathbb 1(X\le t)$. For $Y:\Omega\to[0,1]$ write $|\bar\pi(Y)\rangle=\sum_\omega\sqrt{\pi(\omega)}\frac{\mu_Y-Y(\omega)}{\sqrt{\mu_Y(1-\mu_Y)}}|\omega\rangle$, $\mu_Y=\mathbb E_\pi[Y]$. There are universal $c>0$, $k\in\mathbb N$ and a bidirectional canonical transducer $V=\mathtt{QuantileEst}(X,U,p,\epsilon,M,\Delta,\rho)$ acting as $|\pi\rangle|0\rangle\rightsquigarrow|\pi\rangle|\tilde q_p\rangle$ with complexity at most
--
--   $$c\Big(C_X+W(U,|\pi\rangle)+\sup_{t\in[0,M]}W(U,|\bar\pi(X_t)\rangle)\Big)\cdot\frac1\epsilon\Big(1+\log\frac M\Delta\Big)\log\Big(2+\frac1\rho\Big)\cdot\Big(\log(2+\tfrac1\epsilon)\log(2+\tfrac M\Delta)\log(2+\tfrac1\rho)\Big)^k,$$
--
--   such that a computational-basis measurement of part of $|\tilde q_p\rangle$ yields $q_p$ with $\mathbb P_{x\sim\pi}[X(x)\le q_p]\in[p-3\epsilon,p+3\epsilon]$ with probability at least $1-\rho$.
--
--   The estimator is non-destructive: the state $|\pi\rangle$ is restored.
--
--   **Formalization Note** $|\tilde q_p\rangle$ is a state of an output register initialised to $|0\rangle$, read out by a readout fixed before the input. The supremum is over finitely many values ($X_t$ changes only at the values of $X$).
--
--   Differences from the source:
--   - encoding: states, oracles and constants depend on an implicit input x ∈ D (p.14); the canonical transducers do not → an explicit input type D with oracles O x, data as functions of x, and ∃ transducer before ∀ x; reason: the convention of p.14 made explicit; same instances
--   - encoding: Hilbert spaces V, H, W of the transducers → coordinate spaces ℂ^V over finite types; reason: Part I's transducers are finite-dimensional (pp.4, 36); the published base items use the same model
--   - generalization: a uniform cost bound C_X (one number) → C_X may depend on the input x; reason: the proof composes the bounds input by input; a constant bound is the special case
--   - encoding: a state |µ̃⟩ of which a subset of the qubits is measured → |π⟩ ⊗ φ_x with φ_x on an output register Fin (a+1) × Fin (g+1) starting in |0⟩, a readout val fixed before x, and E, Var, probabilities given by the published readMean, readVar, readProb; reason: the published reading of Theorems 10.2–10.3 (answer and garbage registers)
--   - encoding: a transducer O_X^(t) for every t ∈ [0, M] → a family OX t indexed by t ∈ ℝ, with its own workspace size, and hypotheses for t ∈ [0, M]; reason: same family
--   - reading: Õ(·) / O(· polylog) → universal c > 0 and k ∈ ℕ with a factor (log(2+1/ϵ)·log(2+M/Δ)·log(2+1/ρ))^k; reason: §2.1's Õ with log(2+·) so the factors are ≥ log 2 > 0 for every parameter value (base decisions 3–4)
--   - reading: log(1/ρ) → log(2 + 1/ρ); reason: log(1/ρ) vanishes at ρ = 1 and is negative for ρ > 1 while every estimate costs at least one query; as in the published Theorem 10.3
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Theorem 3.8, p.26 (PDF p.28)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_mm_basic
import Definitions.Def_QVolTransducer_BiCanonical
import Definitions.Def_QVolTransducer_starState
import Definitions.Def_QVolTransducer_readMean
import Definitions.Def_QVolTransducer_Supplement_perpVec

namespace QVolTransducer.Supplement

open QAlgorithms

/-- **Quantile estimator** (Cornelissen, Apers, Gribling, *Improved quantum volume estimation with
transducers and amortized quantum walks*, arXiv:2609.40217 (version of November 3, 2026, sha256
40d7b52d…), Theorem 3.8, p.26 (PDF p.28)).

There are universal constants `c > 0` and `k ∈ ℕ` with the following property. Let `π` be a
probability distribution over a finite set `Ω`, `X : Ω → [0, M]` with `M > 0`, and
`Q_X(p) := inf{t ∈ [0, M] : P_{x∼π}[X(x) ≤ t] ≥ p}`. Let `p ∈ (0, 1)`,
`ϵ ∈ (0, min{p, 1 − p})` and `Δ > 0` with `Q_X(p + ϵ) − Q_X(p − ϵ) ≥ Δ`, and `ρ > 0`. Let `U` be a
bidirectional canonical transducer that reflects through `|π⟩` and, for every `t ∈ [0, M]`,
`O_X^(t)` one with uniform cost bound `C_X` acting as
`|ω⟩|0⟩ ⇝ |ω⟩(√X_t(ω)|1⟩ + √(1 − X_t(ω))|0⟩)`, `X_t := 1/4 + 1(X ≤ t)/2`. Then there is a
bidirectional canonical transducer `V = QuantileEst(X, U, p, ϵ, M, Δ, ρ)` acting as
`|π⟩|0⟩ ⇝ |π⟩|q̃_p⟩` with complexity at most
`c (C_X + W(U,|π⟩) + sup_{t∈[0,M]} W(U,|π̄(X_t)⟩)) · (1/ϵ) · (1 + log(M/Δ)) · log(2 + 1/ρ)
  · (log(2+1/ϵ) log(2+M/Δ) log(2+1/ρ))^k`,
where `|π̄(Y)⟩ = Σ_ω √π(ω)(µ_Y − Y(ω))/√(µ_Y(1 − µ_Y))|ω⟩`, such that a computational-basis
measurement of part of `|q̃_p⟩` yields a value `q_p` with `P_{x∼π}[X(x) ≤ q_p] ∈ [p − 3ϵ, p + 3ϵ]`
with probability at least `1 − ρ`.

**Formalization Note** The implicit input (p.14) is explicit (`D`, `O_x`, `π_x`, `X_x`, `C_X(x)`);
`V`, its output register `Fin (a+1) × Fin (g+1)` (initially `|0⟩`) and its readout `val` are chosen
before `x`; probabilities of the read-out value are the published `readProb`. The tilde hides
polylogarithmic factors in `1/ϵ`, `M/Δ` and `1/ρ`, read as universal `c`, `k` with `log(2+·)`
factors, and the printed `log(1/ρ)` is read `log(2 + 1/ρ)` (as in the published Theorem 10.3). The
supremum is over a family taking finitely many values (`X_t` changes only at the values of `X`),
so it is a maximum. -/
theorem theorem_3_8 :
    ∃ c : ℝ, 0 < c ∧ ∃ k : ℕ,
      ∀ (Ω Q Wu : Type) [Fintype Ω] [DecidableEq Ω] [Fintype Q] [DecidableEq Q]
        [Fintype Wu] [DecidableEq Wu]
        (D : Type) (O : D → Matrix.unitaryGroup Q ℂ) (π X : D → Ω → ℝ) (M : ℝ) (CX : D → ℝ)
        (U : BiCanonical Ω Q Wu) (nX : ℝ → ℕ) (OX : ∀ t, BiCanonical (Ω × Fin 2) Q (Fin (nX t))),
        (∀ x, MarkovMixing.IsDist (π x)) → 0 < M → (∀ x ω, X x ω ∈ Set.Icc 0 M) →
        IsReflectionThrough U O (fun x => sqrtVec (π x)) →
        (∀ t ∈ Set.Icc 0 M, ∀ x (ψ : EuclideanSpace ℂ (Ω × Fin 2)),
          transductionComplexity ((OX t).apply (O x)) ψ ≤ CX x * ‖ψ‖ ^ 2) →
        (∀ t ∈ Set.Icc 0 M, ∀ x ω, Transduces ((OX t).apply (O x)) (ket (ω, (0 : Fin 2)))
          (tensorVec (ket ω) (coinVec (threshVar (X x) t ω)))) →
        ∀ p ϵ Δ ρ : ℝ, 0 < p → p < 1 → 0 < ϵ → ϵ < min p (1 - p) → 0 < Δ → 0 < ρ →
        (∀ x, Δ ≤ quantileFin (π x) (X x) M (p + ϵ) - quantileFin (π x) (X x) M (p - ϵ)) →
        ∃ (a g n : ℕ) (V : BiCanonical (Ω × (Fin (a + 1) × Fin (g + 1))) Q (Fin n))
          (val : Fin (a + 1) → ℝ), ∀ x,
          ∃ (φ : EuclideanSpace ℂ (Fin (a + 1) × Fin (g + 1)))
            (w : EuclideanSpace ℂ ((Q ⊕ Q) × Fin n)),
            TransducesWith (V.apply (O x)) (tensorVec (sqrtVec (π x)) (ket (0, 0)))
              (tensorVec (sqrtVec (π x)) φ) w ∧
            ‖w‖ ^ 2 ≤ c * (CX x + transductionComplexity (U.apply (O x)) (sqrtVec (π x)) +
                ⨆ t : Set.Icc (0 : ℝ) M, transductionComplexity (U.apply (O x))
                  (perpVec (π x) (threshVar (X x) t))) *
              (1 / ϵ) * (1 + Real.log (M / Δ)) * Real.log (2 + 1 / ρ) *
              (Real.log (2 + 1 / ϵ) * Real.log (2 + M / Δ) * Real.log (2 + 1 / ρ)) ^ k ∧
            1 - ρ ≤ readProb φ val (fun q =>
              probLe (π x) (X x) q ∈ Set.Icc (p - 3 * ϵ) (p + 3 * ϵ)) := by sorry

end QVolTransducer.Supplement
