-- Prove2me | Theorems.Thm_QVolTransducer_Supplement_theorem_3_5
-- name    : QVolTransducer.Supplement.theorem_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:37:03.429448+00:00
-- url     : https://prove2.me/theorems/2e3a0152-9b5a-4dde-b72d-c7985f4bd6e9
-- title:
--   Theorem 3.5 — annealing transducer $|\varphi\rangle\rightsquigarrow\langle\chi|\varphi\rangle|\chi\rangle/|\langle\chi|\varphi\rangle|$ from two reflections
-- statement:
--   Let $|\varphi\rangle,|\chi\rangle\in\mathcal H$ be states with $0<|\langle\chi|\varphi\rangle|<1$, and let $R_{|\varphi\rangle}$ and $R_{|\chi\rangle}$ be bidirectional canonical transducers that reflect through $|\varphi\rangle$ and $|\chi\rangle$. Put
--
--   $$|\bar\chi\rangle=\frac{|\varphi\rangle-\langle\chi|\varphi\rangle|\chi\rangle}{\||\varphi\rangle-\langle\chi|\varphi\rangle|\chi\rangle\|},\qquad |\bar\varphi\rangle=-\frac{|\chi\rangle-\langle\varphi|\chi\rangle|\varphi\rangle}{\||\chi\rangle-\langle\varphi|\chi\rangle|\varphi\rangle\|}\cdot\frac{\langle\chi|\varphi\rangle}{|\langle\chi|\varphi\rangle|}.$$
--
--   There is a universal constant $c>0$ such that one can construct a bidirectional canonical transducer $U$ mapping $|\varphi\rangle$ to $\langle\chi|\varphi\rangle|\chi\rangle/|\langle\chi|\varphi\rangle|$ with transduction complexity
--
--   $$W(U,|\varphi\rangle)\le c\,\frac{W(R_{|\chi\rangle},|\chi\rangle)+W(R_{|\varphi\rangle},|\varphi\rangle)+(1-|\langle\chi|\varphi\rangle|^4)\,W(R_{|\chi\rangle},|\bar\chi\rangle)+(1-|\langle\chi|\varphi\rangle|^2)\,W(R_{|\varphi\rangle},|\bar\varphi\rangle)}{|\langle\chi|\varphi\rangle|}.$$
--
--   In particular $W(U,|\varphi\rangle)\in O\big((W(R_{|\chi\rangle},|\chi\rangle)+W(R_{|\chi\rangle},|\bar\chi\rangle)+W(R_{|\varphi\rangle},|\varphi\rangle)+W(R_{|\varphi\rangle},|\bar\varphi\rangle))/|\langle\chi|\varphi\rangle|\big)$. This generalizes Grover's iterate to two costly reflections and is the basic annealing step.
--
--   **Formalization Note** States, oracles and the input set are explicit (implicit-input convention, p.14); the transducers are chosen before the input; the states are unit vectors of $\mathbb C^V$.
--
--   Differences from the source:
--   - encoding: states, oracles and constants depend on an implicit input x ∈ D (p.14); the canonical transducers do not → an explicit input type D with oracles O x, data as functions of x, and ∃ transducer before ∀ x; reason: the convention of p.14 made explicit; same instances
--   - encoding: Hilbert spaces V, H, W of the transducers → coordinate spaces ℂ^V over finite types; reason: Part I's transducers are finite-dimensional (pp.4, 36); the published base items use the same model
--   - reading: |φ⟩, |χ⟩ ∈ H → unit vectors (‖φ_x‖ = ‖χ_x‖ = 1); reason: they are states (p.22: 'we are given a state |φ⟩'); the proof uses ‖ψ₁‖ = |⟨χ|φ⟩| and ‖ψ₀‖ = √(1 − |⟨χ|φ⟩|²), which needs unit vectors
--   - reading: O(·) → a universal constant c > 0 chosen before every parameter, input and transducer; reason: §2.1's O-notation with the quantification of the published base theorems (base decisions 3–4)
--   - reading: the chain W(U,|φ⟩) ∈ O(first bound) ⊆ O(second bound) → the first (sharper) bound; reason: the second follows from the first since 0 ≤ 1 − |⟨χ|φ⟩|⁴, 1 − |⟨χ|φ⟩|² ≤ 1
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Theorem 3.5, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_QVolTransducer_BiCanonical
import Definitions.Def_QVolTransducer_Supplement_perpVec

namespace QVolTransducer.Supplement

/-- **Annealing transducer from two state-reflection transducers** (Cornelissen, Apers, Gribling,
*Improved quantum volume estimation with transducers and amortized quantum walks*, arXiv:2609.40217
(version of November 3, 2026, sha256 40d7b52d…), Theorem 3.5, p.22 (PDF p.24)).

There is a universal constant `c > 0` with the following property. Let `|φ⟩, |χ⟩ ∈ ℋ` be states
with `0 < |⟨χ|φ⟩| < 1`, and let `R_{|φ⟩}`, `R_{|χ⟩}` be bidirectional canonical transducers that
reflect through `|φ⟩` and `|χ⟩`. Then there is a bidirectional canonical transducer `U` that maps
`|φ⟩` to `⟨χ|φ⟩|χ⟩/|⟨χ|φ⟩|` with transduction complexity at most
`c (W(R_{|χ⟩}, |χ⟩) + W(R_{|φ⟩}, |φ⟩) + (1 − |⟨χ|φ⟩|⁴) W(R_{|χ⟩}, |χ̄⟩)
  + (1 − |⟨χ|φ⟩|²) W(R_{|φ⟩}, |φ̄⟩)) / |⟨χ|φ⟩|`,
where `|χ̄⟩ = (|φ⟩ − ⟨χ|φ⟩|χ⟩)/‖|φ⟩ − ⟨χ|φ⟩|χ⟩‖` and
`|φ̄⟩ = −(|χ⟩ − ⟨φ|χ⟩|φ⟩)/‖|χ⟩ − ⟨φ|χ⟩|φ⟩‖ · ⟨χ|φ⟩/|⟨χ|φ⟩|` (p.22).

**Formalization Note** Everything depends on the implicit input (p.14): `D` is the input set with
oracles `O_x ∈ U(ℂ^Q)`, the states `φ_x, χ_x ∈ ℂ^V` are unit vectors, and the transducers (`R_φ`,
`R_χ`, `U`) are chosen before `x`. `O(·)` is a universal constant `c` chosen before everything. The
printed second, coarser bound `O((W(R_χ,χ) + W(R_χ,χ̄) + W(R_φ,φ) + W(R_φ,φ̄))/|⟨χ|φ⟩|)` follows
from the first. `W(R, ·)` is the published `transductionComplexity`. -/
theorem theorem_3_5 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (V Q Wφ Wχ : Type) [Fintype V] [DecidableEq V] [Fintype Q] [DecidableEq Q]
        [Fintype Wφ] [DecidableEq Wφ] [Fintype Wχ] [DecidableEq Wχ]
        (D : Type) (O : D → Matrix.unitaryGroup Q ℂ) (φ χ : D → EuclideanSpace ℂ V)
        (Rφ : BiCanonical V Q Wφ) (Rχ : BiCanonical V Q Wχ),
        (∀ x, ‖φ x‖ = 1) → (∀ x, ‖χ x‖ = 1) →
        (∀ x, 0 < ‖inner ℂ (χ x) (φ x)‖) → (∀ x, ‖inner ℂ (χ x) (φ x)‖ < 1) →
        IsReflectionThrough Rφ O φ → IsReflectionThrough Rχ O χ →
        ∃ (n : ℕ) (U : BiCanonical V Q (Fin n)), ∀ x,
          TransducesWithin (U.apply (O x)) (φ x)
            ((inner ℂ (χ x) (φ x) / ((‖inner ℂ (χ x) (φ x)‖ : ℝ) : ℂ)) • χ x)
            (c * (transductionComplexity (Rχ.apply (O x)) (χ x) +
                transductionComplexity (Rφ.apply (O x)) (φ x) +
                (1 - ‖inner ℂ (χ x) (φ x)‖ ^ 4) *
                  transductionComplexity (Rχ.apply (O x)) (annealPerpChi (χ x) (φ x)) +
                (1 - ‖inner ℂ (χ x) (φ x)‖ ^ 2) *
                  transductionComplexity (Rφ.apply (O x)) (annealPerpPhi (χ x) (φ x))) /
              ‖inner ℂ (χ x) (φ x)‖) := by sorry

end QVolTransducer.Supplement
