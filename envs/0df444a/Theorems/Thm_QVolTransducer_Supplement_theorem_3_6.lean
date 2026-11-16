-- Prove2me | Theorems.Thm_QVolTransducer_Supplement_theorem_3_6
-- name    : QVolTransducer.Supplement.theorem_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:37:48.368221+00:00
-- url     : https://prove2.me/theorems/5bce4305-269f-45c5-ba7f-9048a3f52f0b
-- title:
--   Theorem 3.6 — rejection sampling transducer
-- statement:
--   Let $\pi$ be a distribution over a finite set $\Omega$, $a:\Omega\to[0,1]$, $A=\mathbb E_{\omega\sim\pi}[a(\omega)]$, and
--
--   $$|\pi\rangle=\sum_\omega\sqrt{\pi(\omega)}|\omega\rangle,\quad |\pi^{(a)}\rangle=\sum_\omega\sqrt{\tfrac{\pi(\omega)a(\omega)}{A}}|\omega\rangle,\quad |\bar\pi\rangle=\sum_\omega\sqrt{\pi(\omega)}\,\frac{A-a(\omega)}{\sqrt{A(1-A)}}|\omega\rangle.$$
--
--   Let $U$ be a bidirectional canonical transducer that reflects through $|\pi\rangle$, and $O^{(a)}$ a bidirectional canonical transducer on $\mathbb C^\Omega\otimes\mathbb C^2$ with uniform cost bound $C^{(a)}$ (i.e. $W(O^{(a)},|\psi\rangle)\le C^{(a)}\||\psi\rangle\|^2$ for all $|\psi\rangle$) mapping $|\omega\rangle|0\rangle\rightsquigarrow|\omega\rangle(\sqrt{a(\omega)}|1\rangle+\sqrt{1-a(\omega)}|0\rangle)$. There is a universal $c>0$ such that one can build bidirectional canonical transducers $C$ and $V$ with
--
--   1. $|\pi\rangle\overset{C}{\rightsquigarrow}|\pi^{(a)}\rangle$ with complexity at most $c\,\big(C^{(a)}+W(U,|\pi\rangle)+(1-A)W(U,|\bar\pi\rangle)\big)/\sqrt A$;
--   2. $|\pi^{(a)}\rangle\overset{V}{\rightsquigarrow}|\pi^{(a)}\rangle$ with complexity at most $c\,\big(C^{(a)}+W(U,|\pi\rangle)\big)/A$;
--   3. $|\bar\pi^{(a)}\rangle\overset{V}{\rightsquigarrow}-|\bar\pi^{(a)}\rangle$ with complexity at most $c\big(C^{(a)}\||\bar\pi^{(a)}\rangle\|^2+A\cdot W\big(U,\sum_\omega\tfrac{\bar\pi^{(a)}(\omega)}{\sqrt{\pi(\omega)}}|\omega\rangle\big)\big)$ for every $|\bar\pi^{(a)}\rangle\in\mathbb C^\Omega$ with $\langle\bar\pi^{(a)}|\pi^{(a)}\rangle=0$, where $\bar\pi^{(a)}(\omega)=\sqrt{\pi^{(a)}(\omega)}\,\langle\omega|\bar\pi^{(a)}\rangle$.
--
--   This is rejection sampling at the level of transducers: it prepares and reflects through the posterior state using the same implicit oracles.
--
--   **Formalization Note** The states are defined only when $0<A<1$, which is assumed. In item 3 the vector $\sum_\omega\bar\pi^{(a)}(\omega)/\sqrt{\pi(\omega)}\,|\omega\rangle$ is written $A^{-1/2}\sum_\omega\sqrt{a(\omega)}\langle\omega|\bar\pi^{(a)}\rangle|\omega\rangle$, the vector the proof feeds to $U$.
--
--   Differences from the source:
--   - encoding: states, oracles and constants depend on an implicit input x ∈ D (p.14); the canonical transducers do not → an explicit input type D with oracles O x, data as functions of x, and ∃ transducer before ∀ x; reason: the convention of p.14 made explicit; same instances
--   - encoding: Hilbert spaces V, H, W of the transducers → coordinate spaces ℂ^V over finite types; reason: Part I's transducers are finite-dimensional (pp.4, 36); the published base items use the same model
--   - reading: the states |π^(a)⟩ and |π̄⟩ (defined only when 0 < A < 1) → hypotheses 0 < A and A < 1; reason: the formulas divide by √A and √(A(1 − A)); the proof applies Corollary 3.4 with ‖π₀‖² = 1 − A, ‖π₁‖² = A, which needs both positive
--   - generalization: a uniform cost bound C^(a) (one number) → C^(a) may depend on the input x; reason: the proof composes the bounds input by input; a constant bound is the special case
--   - reading: Σ_ω π̄^(a)(ω)/√π(ω) (with π̄^(a)(ω) = √π^(a)(ω)·⟨ω|π̄^(a)⟩) → A^{−1/2} Σ_ω √a(ω) ⟨ω|π̄^(a)⟩ |ω⟩; reason: equal wherever π(ω) > 0; where π(ω) = 0 the printed quotient is 0/0, and the latter is the vector (I ⊗ ⟨0|)(O^(a))†|π̄^(a)⟩|1⟩/√A of the proof (p.25)
--   - generalization: for all states |π̄^(a)⟩ ∈ ℂ^Ω with ⟨π̄^(a)|π^(a)⟩ = 0 → for all vectors v ∈ ℂ^Ω with ⟨v|π^(a)⟩ = 0; reason: the action is linear and both sides of the bound scale by |λ|² under v ↦ λv, so unit vectors are a special case
--   - reading: O(·) → a universal constant c > 0 chosen before every parameter, input and transducer; reason: §2.1's O-notation with the quantification of the published base theorems (base decisions 3–4)
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Theorem 3.6, p.24 (PDF p.26)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_mm_basic
import Definitions.Def_QVolTransducer_BiCanonical
import Definitions.Def_QVolTransducer_starState
import Definitions.Def_QVolTransducer_Supplement_perpVec

namespace QVolTransducer.Supplement

open QAlgorithms

/-- **Rejection sampling transducer** (Cornelissen, Apers, Gribling, *Improved quantum volume
estimation with transducers and amortized quantum walks*, arXiv:2609.40217 (version of November 3,
2026, sha256 40d7b52d…), Theorem 3.6, p.24 (PDF p.26)).

There is a universal constant `c > 0` with the following property. Let `π` be a distribution over a
finite set `Ω`, `a : Ω → [0, 1]`, `A = E_{ω∼π}[a(ω)]`, `|π⟩ = Σ_ω √π(ω)|ω⟩`,
`|π^(a)⟩ = Σ_ω √(π(ω)a(ω)/A)|ω⟩` and `|π̄⟩ = Σ_ω √π(ω)(A − a(ω))/√(A(1 − A))|ω⟩`. Let `U` be a
bidirectional canonical transducer that reflects through `|π⟩`, and `O^(a)` a bidirectional
canonical transducer on `ℂ^Ω ⊗ ℂ²` with uniform cost bound `C^(a)` (`W(O^(a), |ψ⟩) ≤ C^(a)‖|ψ⟩‖²`
for all `|ψ⟩`) mapping `|ω⟩|0⟩ ⇝ |ω⟩(√a(ω)|1⟩ + √(1 − a(ω))|0⟩)` for every `ω`. Then there are
bidirectional canonical transducers `C` and `V` with
1. `|π⟩ ⇝_C |π^(a)⟩` with complexity at most `c (C^(a) + W(U,|π⟩) + (1 − A) W(U,|π̄⟩))/√A`;
2. `|π^(a)⟩ ⇝_V |π^(a)⟩` with complexity at most `c (C^(a) + W(U,|π⟩))/A`;
3. `|π̄^(a)⟩ ⇝_V −|π̄^(a)⟩` with complexity at most
   `c (C^(a) ‖|π̄^(a)⟩‖² + A · W(U, Σ_ω π̄^(a)(ω)/√π(ω) |ω⟩))` for every `|π̄^(a)⟩ ∈ ℂ^Ω` with
   `⟨π̄^(a)|π^(a)⟩ = 0`, where `π̄^(a)(ω) := √(π^(a)(ω)) ⟨ω|π̄^(a)⟩`.

**Formalization Note** The implicit input (p.14) is explicit: `D`, oracles `O_x`, and `π_x`, `a_x`,
`C^(a)_x` depending on `x`; the transducers are chosen before `x`. The states are defined only when
`0 < A < 1` ("where the states are defined"), which is assumed. In item 3 the vector
`Σ_ω π̄^(a)(ω)/√π(ω)|ω⟩` is written `A^{−1/2} Σ_ω √a(ω) ⟨ω|π̄^(a)⟩ |ω⟩`: both agree wherever
`π(ω) > 0`, and the latter is the vector the proof feeds to `U` (p.25) and is defined everywhere.
Item 3 is stated for every vector, not only unit ones (both sides scale by `|λ|²`). `O(·)` is a
universal constant `c`. -/
theorem theorem_3_6 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (Ω Q Wu Wa : Type) [Fintype Ω] [DecidableEq Ω] [Fintype Q] [DecidableEq Q]
        [Fintype Wu] [DecidableEq Wu] [Fintype Wa] [DecidableEq Wa]
        (D : Type) (O : D → Matrix.unitaryGroup Q ℂ) (π a : D → Ω → ℝ) (Ca : D → ℝ)
        (U : BiCanonical Ω Q Wu) (Oa : BiCanonical (Ω × Fin 2) Q Wa),
        (∀ x, MarkovMixing.IsDist (π x)) → (∀ x ω, a x ω ∈ Set.Icc (0 : ℝ) 1) →
        (∀ x, 0 < finMean (π x) (a x)) → (∀ x, finMean (π x) (a x) < 1) →
        IsReflectionThrough U O (fun x => sqrtVec (π x)) →
        (∀ x (ψ : EuclideanSpace ℂ (Ω × Fin 2)),
          transductionComplexity (Oa.apply (O x)) ψ ≤ Ca x * ‖ψ‖ ^ 2) →
        (∀ x ω, Transduces (Oa.apply (O x)) (ket (ω, (0 : Fin 2)))
          (tensorVec (ket ω) (coinVec (a x ω)))) →
        ∃ (nC nV : ℕ) (C : BiCanonical Ω Q (Fin nC)) (V : BiCanonical Ω Q (Fin nV)), ∀ x,
          TransducesWithin (C.apply (O x)) (sqrtVec (π x)) (rejVec (π x) (a x))
            (c * (Ca x + transductionComplexity (U.apply (O x)) (sqrtVec (π x)) +
                (1 - finMean (π x) (a x)) *
                  transductionComplexity (U.apply (O x)) (perpVec (π x) (a x))) /
              Real.sqrt (finMean (π x) (a x))) ∧
          TransducesWithin (V.apply (O x)) (rejVec (π x) (a x)) (rejVec (π x) (a x))
            (c * (Ca x + transductionComplexity (U.apply (O x)) (sqrtVec (π x))) /
              finMean (π x) (a x)) ∧
          ∀ v : EuclideanSpace ℂ Ω, inner ℂ v (rejVec (π x) (a x)) = 0 →
            TransducesWithin (V.apply (O x)) v (-v)
              (c * (Ca x * ‖v‖ ^ 2 + finMean (π x) (a x) *
                transductionComplexity (U.apply (O x))
                  (WithLp.toLp 2 (fun ω => ((Real.sqrt (a x ω) /
                    Real.sqrt (finMean (π x) (a x)) : ℝ) : ℂ) * v ω)))) := by sorry

end QVolTransducer.Supplement
