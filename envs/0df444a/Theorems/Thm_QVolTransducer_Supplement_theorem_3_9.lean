-- Prove2me | Theorems.Thm_QVolTransducer_Supplement_theorem_3_9
-- name    : QVolTransducer.Supplement.theorem_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:40:17.379198+00:00
-- url     : https://prove2.me/theorems/9deeae23-b185-46bf-af2a-0b9e637290af
-- title:
--   Theorem 3.9 — mean estimation MeanEst under a perturbed reflection
-- statement:
--   Let $\pi,\tilde\pi$ be distributions over a finite set $\Omega$ with $\|\pi-\tilde\pi\|_{\mathrm{TV}}\le\eta$, $\eta\ge0$, and $X:\Omega\to\mathbb R$; write $|\tilde\pi\rangle=\sum_\omega\sqrt{\tilde\pi(\omega)}|\omega\rangle$, $\mu_X=\mathbb E_\pi[X]$, and for $Y:\Omega\to[0,1]$, $|\bar\pi(Y)\rangle=\sum_\omega\sqrt{\tilde\pi(\omega)}\frac{\tilde\mu_Y-Y(\omega)}{\sqrt{\tilde\mu_Y(1-\tilde\mu_Y)}}|\omega\rangle$ with $\tilde\mu_Y=\mathbb E_{\tilde\pi}[Y]$. Let $U$ reflect through $|\tilde\pi\rangle$. Suppose $\mathrm{Var}_\pi[X]\le\tilde\sigma^2$ and $\tilde m\in[0,M]$ with $|\tilde m-\mu_X|\le17\tilde\sigma$; let $t\ge1$, $\epsilon\in(0,1)$, $k=\lceil\log(580/\epsilon)\rceil$, $a_j=2^j\tilde\sigma$, $a_{-1}=0$, $B_j=\min\{1,580/2^{2j}\}$ and
--
--   $$Y_j^\pm(\omega):=\frac{B_j}4+\Big(1-\frac{B_j}2\Big)\cdot\frac{\pm(X(\omega)-\tilde m)}{a_j}\cdot\mathbb 1_{\pm(X(\omega)-\tilde m)\in(a_{j-1},a_j]}.$$
--
--   Suppose that for every $j\in\{0,\dots,k\}$ and sign $\pm$ a transducer $O_X^{(j,\pm)}$ with uniform cost bound $C_X$ implements $|\omega\rangle|0\rangle\rightsquigarrow|\omega\rangle(\sqrt{Y_j^\pm(\omega)}|1\rangle+\sqrt{1-Y_j^\pm(\omega)}|0\rangle)$. Then there are universal $c>0$, $k'\in\mathbb N$ and a bidirectional canonical transducer $V=\mathtt{MeanEst}(X,U,\tilde m,\tilde\sigma,t,\epsilon)$ acting as $|\tilde\pi\rangle|0\rangle\rightsquigarrow|\tilde\pi\rangle|\bar\mu_X\rangle$ with complexity at most
--
--   $$c\sum_{j=0}^k\sum_\pm\big(C_X+W(U,|\tilde\pi\rangle)+W(U,|\bar\pi(Y_j^\pm)\rangle)\big)\cdot t\cdot\big(\log(2+t)\log(2+1/\epsilon)\big)^{k'},$$
--
--   such that the measured value $\bar\mu_X$ satisfies
--
--   $$|\mathbb E[\bar\mu_X]-\mu_X|\le\Big(\epsilon+2^{14}\frac\eta\epsilon\Big)\tilde\sigma,\qquad\mathrm{Var}[\bar\mu_X]\le\Big(\frac1{t^2}+2^{32}\frac{\eta}{\epsilon^2}\Big)\tilde\sigma^2.$$
--
--   This unbounded mean estimator tolerates a reflection through a state that only approximates the target distribution, which is what the volume algorithm can implement.
--
--   **Formalization Note** $k=\lceil\log_2(580/\epsilon)\rceil$; $\tilde\sigma>0$; the output register is initialised to $|0\rangle$; $V$, the register and the readout are chosen before the input.
--
--   Differences from the source:
--   - encoding: states, oracles and constants depend on an implicit input x ∈ D (p.14); the canonical transducers do not → an explicit input type D with oracles O x, data as functions of x, and ∃ transducer before ∀ x; reason: the convention of p.14 made explicit; same instances
--   - encoding: Hilbert spaces V, H, W of the transducers → coordinate spaces ℂ^V over finite types; reason: Part I's transducers are finite-dimensional (pp.4, 36); the published base items use the same model
--   - generalization: a uniform cost bound C_X (one number) → C_X may depend on the input x; reason: the proof composes the bounds input by input; a constant bound is the special case
--   - encoding: a state |µ̃⟩ of which a subset of the qubits is measured → |π⟩ ⊗ φ_x with φ_x on an output register Fin (a+1) × Fin (g+1) starting in |0⟩, a readout val fixed before x, and E, Var, probabilities given by the published readMean, readVar, readProb; reason: the published reading of Theorems 10.2–10.3 (answer and garbage registers)
--   - reading: k = ⌈log(580/ϵ)⌉ → k = ⌈log₂(580/ϵ)⌉; reason: the proof (p.28) uses a_k = 2^k σ̃ ≥ 580σ̃/ϵ and 2^k ≤ 1160/ϵ, i.e. base 2
--   - reading: m̃ ∈ [0, M] with M never introduced → M a free real parameter and the hypothesis 0 ≤ m̃ ≤ M; reason: M occurs only in this hypothesis
--   - encoding: σ̃ with Var_π[X] ≤ σ̃² → σ̃ > 0; reason: a_j = 2^j σ̃ is a denominator in Y_j^±; the condition only excludes the undefined case σ̃ ≤ 0
--   - reading: a transducer O_X^(j,±) → a bidirectional canonical transducer; reason: the proof composes them with Theorem 3.7, which requires bidirectional canonical transducers
--   - reading: Σ_{j=0}^k (C_X + W(U,|π̃⟩) + W(U,|π̄(Y_j^±)⟩)) → the sum over j = 0, …, k and both signs ±; reason: the proof (p.28) builds one estimator V_j^± for each j and sign
--   - reading: Õ(·) / O(· polylog) → universal c > 0 and k ∈ ℕ with a factor (log(2+t)·log(2+1/ϵ))^k; reason: §2.1's Õ with log(2+·) so the factors are ≥ log 2 > 0 for every parameter value (base decisions 3–4)
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Theorem 3.9, p.27 (PDF p.29)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_mm_basic
import Definitions.Def_QVolTransducer_BiCanonical
import Definitions.Def_QVolTransducer_starState
import Definitions.Def_QVolTransducer_readMean
import Definitions.Def_QVolTransducer_Supplement_perpVec

namespace QVolTransducer.Supplement

open QAlgorithms

/-- **Mean estimation under a perturbed reflection** (Cornelissen, Apers, Gribling, *Improved
quantum volume estimation with transducers and amortized quantum walks*, arXiv:2609.40217 (version
of November 3, 2026, sha256 40d7b52d…), Theorem 3.9, p.27 (PDF p.29)).

There are universal constants `c > 0` and `k' ∈ ℕ` with the following property. Let `π, π̃` be
distributions over a finite set `Ω` with `‖π − π̃‖_TV ≤ η`, `η ≥ 0`, `X : Ω → ℝ`,
`|π̃⟩ = Σ_ω √π̃(ω)|ω⟩`, `µ_X = E_π[X]`, and for `Y : Ω → [0, 1]`
`|π̄(Y)⟩ = Σ_ω √π̃(ω)(µ̃_Y − Y(ω))/√(µ̃_Y(1 − µ̃_Y))|ω⟩` with `µ̃_Y = E_π̃[Y]`. Let `U` reflect
through `|π̃⟩`. Suppose `Var_π[X] ≤ σ̃²` and `m̃ ∈ [0, M]` with `|m̃ − µ_X| ≤ 17σ̃`; let `t ≥ 1`,
`ϵ ∈ (0, 1)`, `k = ⌈log(580/ϵ)⌉`, `a_j = 2^j σ̃`, `a_{−1} = 0`, `B_j = min{1, 580/2^{2j}}` and
`Y_j^±(ω) := B_j/4 + (1 − B_j/2) · ±(X(ω) − m̃)/a_j · 1_{±(X(ω) − m̃) ∈ (a_{j−1}, a_j]}`. Suppose that
for every `j ∈ {0, …, k}` and sign `±`, `O_X^(j,±)` has uniform cost bound `C_X` and implements
`|ω⟩|0⟩ ⇝ |ω⟩(√Y_j^±(ω)|1⟩ + √(1 − Y_j^±(ω))|0⟩)`. Then there is a bidirectional canonical
transducer `V = MeanEst(X, U, m̃, σ̃, t, ϵ)` acting as `|π̃⟩|0⟩ ⇝ |π̃⟩|µ̄_X⟩` with complexity at most
`c Σ_{j=0}^{k} Σ_± (C_X + W(U,|π̃⟩) + W(U,|π̄(Y_j^±)⟩)) · t · (log(2+t) log(2+1/ϵ))^{k'}` such that
the read-out value `µ̄_X` satisfies `|E[µ̄_X] − µ_X| ≤ (ϵ + 2^14 η/ϵ)σ̃` and
`Var[µ̄_X] ≤ (1/t² + 2^32 η/ϵ²)σ̃²`.

**Formalization Note** The implicit input (p.14) is explicit (`D`, `O_x`, `π_x`, `π̃_x`, `X_x`,
`C_X(x)`); `η`, `m̃`, `σ̃`, `M`, `t`, `ϵ` are parameters, and `V`, its output register
`Fin (a+1) × Fin (g+1)` (initially `|0⟩`) and its readout are chosen before `x`. `k` is
`⌈log₂(580/ϵ)⌉` (`meanEstK`: the proof uses `2^k ≥ 580/ϵ` and `2^k ≤ 1160/ϵ`), the sum in the
complexity runs over `j = 0, …, k` and both signs, and `M` (which appears only in `m̃ ∈ [0, M]`) is
a free parameter. `σ̃ > 0` is assumed (`a_j = 2^j σ̃` is a denominator in `Y_j^±`). The oracles
`O_X^(j,±)` ("a transducer", p.27) are bidirectional canonical, as Theorem 3.7, which the proof
invokes, requires. `Õ(·polylog(t, 1/ϵ))` is read as universal `c`, `k'` with `log(2+·)` factors. -/
theorem theorem_3_9 :
    ∃ c : ℝ, 0 < c ∧ ∃ k' : ℕ,
      ∀ (Ω Q Wu : Type) [Fintype Ω] [DecidableEq Ω] [Fintype Q] [DecidableEq Q]
        [Fintype Wu] [DecidableEq Wu]
        (D : Type) (O : D → Matrix.unitaryGroup Q ℂ) (π πt X : D → Ω → ℝ) (CX : D → ℝ)
        (η σt mt M t ϵ : ℝ)
        (U : BiCanonical Ω Q Wu) (nX : ℕ → Bool → ℕ)
        (OX : ∀ j s, BiCanonical (Ω × Fin 2) Q (Fin (nX j s))),
        (∀ x, MarkovMixing.IsDist (π x)) → (∀ x, MarkovMixing.IsDist (πt x)) → 0 ≤ η →
        (∀ x, finTV (π x) (πt x) ≤ η) →
        IsReflectionThrough U O (fun x => sqrtVec (πt x)) →
        0 < σt → (∀ x, finVar (π x) (X x) ≤ σt ^ 2) → mt ∈ Set.Icc 0 M →
        (∀ x, |mt - finMean (π x) (X x)| ≤ 17 * σt) → 1 ≤ t → 0 < ϵ → ϵ < 1 →
        (∀ j ≤ meanEstK ϵ, ∀ s x (ψ : EuclideanSpace ℂ (Ω × Fin 2)),
          transductionComplexity ((OX j s).apply (O x)) ψ ≤ CX x * ‖ψ‖ ^ 2) →
        (∀ j ≤ meanEstK ϵ, ∀ s x ω, Transduces ((OX j s).apply (O x)) (ket (ω, (0 : Fin 2)))
          (tensorVec (ket ω) (coinVec (meanEstY (X x) mt σt j s ω)))) →
        ∃ (a g n : ℕ) (V : BiCanonical (Ω × (Fin (a + 1) × Fin (g + 1))) Q (Fin n))
          (val : Fin (a + 1) → ℝ), ∀ x,
          ∃ (φ : EuclideanSpace ℂ (Fin (a + 1) × Fin (g + 1)))
            (w : EuclideanSpace ℂ ((Q ⊕ Q) × Fin n)),
            TransducesWith (V.apply (O x)) (tensorVec (sqrtVec (πt x)) (ket (0, 0)))
              (tensorVec (sqrtVec (πt x)) φ) w ∧
            ‖w‖ ^ 2 ≤ c * (∑ j ∈ Finset.range (meanEstK ϵ + 1), ∑ s : Bool,
                (CX x + transductionComplexity (U.apply (O x)) (sqrtVec (πt x)) +
                  transductionComplexity (U.apply (O x))
                    (perpVec (πt x) (meanEstY (X x) mt σt j s)))) *
              t * (Real.log (2 + t) * Real.log (2 + 1 / ϵ)) ^ k' ∧
            |readMean φ val - finMean (π x) (X x)| ≤ (ϵ + 2 ^ 14 * η / ϵ) * σt ∧
            readVar φ val ≤ (1 / t ^ 2 + 2 ^ 32 * η / ϵ ^ 2) * σt ^ 2 := by sorry

end QVolTransducer.Supplement
