-- Prove2me | Theorems.Thm_QVolTransducer_corollary_3_4
-- name    : QVolTransducer.corollary_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:24:42.578468+00:00
-- url     : https://prove2.me/theorems/142786af-8b8f-4216-b1b3-989f4193926d
-- title:
--   Corollary 3.4 — amplitude amplification and reflection transducers
-- statement:
--   There is a universal constant $c>0$ with the following property. Let $D$ be a set of inputs with oracles $O_x$, and for every $x\in D$ let $|\psi_0\rangle,|\psi_1\rangle\in\mathcal V$ with $\||\psi_0\rangle\|^2+\||\psi_1\rangle\|^2=1$ and $\||\psi_0\rangle\|,\||\psi_1\rangle\|>0$. Write
--
--   $$
--   |\psi\rangle=|\psi_0\rangle|0\rangle+|\psi_1\rangle|1\rangle,\qquad
--   |\bar\psi\rangle=\frac{\||\psi_1\rangle\|}{\||\psi_0\rangle\|}|\psi_0\rangle|0\rangle-\frac{\||\psi_0\rangle\|}{\||\psi_1\rangle\|}|\psi_1\rangle|1\rangle .
--   $$
--
--   Suppose a bidirectional canonical transducer $R$ acts as a reflection through $|\psi\rangle$ on $\mathcal V\otimes\mathbb C^2$. Then there are bidirectional canonical transducers $C$ and $U$ with
--
--   1. $|\psi\rangle\overset{C}{\rightsquigarrow}\frac{|\psi_1\rangle|1\rangle}{\||\psi_1\rangle\|}$ with complexity at most $c\,\frac{W(R,|\psi\rangle)+\||\psi_0\rangle\|^2W(R,|\bar\psi\rangle)}{\||\psi_1\rangle\|}$;
--   2. $\frac{|\psi_1\rangle}{\||\psi_1\rangle\|}\overset{U}{\rightsquigarrow}\frac{|\psi_1\rangle}{\||\psi_1\rangle\|}$ with complexity at most $c\,\frac{W(R,|\psi\rangle)}{\||\psi_1\rangle\|^2}$;
--   3. $|\perp\rangle\overset{U}{\rightsquigarrow}-|\perp\rangle$ with complexity at most $c\,W(R,|\perp\rangle|1\rangle)$, for all $|\perp\rangle\in\mathcal V$ with $\langle\perp|\psi_1\rangle=0$.
--
--   This is exact amplitude amplification at the level of transducers, without garbage, which the quantum walk of Theorem 4.7 needs.
--
--   Differences from the source:
--   - reading: V a Hilbert space (and the oracle space and workspaces) → finite-dimensional coordinate spaces over finite index types; reason: the transduction complexity W(R, ·) in the conclusion is the minimum of Definition 2.7, which exists in finite dimension (Theorem 2.8); Part II applies the corollary only in finite dimension (p.36)
--   - reading: the implicit input (ψ₀, ψ₁ and R's action depend on it; V does not) → an explicit input set D with oracles O_x and vectors ψ₀(x), ψ₁(x); C and U are single canonical transducers for all inputs; reason: proof of the corollary, p.21, and Definition 2.10
--   - reading: R acts as a reflection through |ψ⟩ on V ⊗ ℂ² → |ψ⟩ ⇝_R |ψ⟩ and |φ⟩ ⇝_R −|φ⟩ for every |φ⟩ ∈ V ⊗ ℂ² orthogonal to |ψ⟩; reason: definition of a reflection transducer (Theorem 2.4, Lemma 4.5)
--   - encoding: O(·) complexity → ∃ universal c > 0 fixed before every parameter, K and ζ, with W ≤ c·(bound); reason: paper.md decision 4
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Corollary 3.4, pp.20–21 (PDF pp.22–23)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QVolTransducer_BiCanonical
import Definitions.Def_QVolTransducer_ampState

namespace QVolTransducer

open QAlgorithms

/-- **Amplitude amplification and reflection transducer** (Cornelissen, Apers, Gribling, *Improved
quantum volume estimation with transducers and amortized quantum walks*, arXiv:2609.40217 (version
of November 3, 2026, sha256 40d7b52d…), Corollary 3.4, pp.20–21 (PDF pp.22–23)).

There is a universal constant `c > 0` with the following property. Let `D` be the (implicit) set of
inputs, with oracles `O_x ∈ U(H)`, and for every `x ∈ D` let `|ψ_0⟩, |ψ_1⟩ ∈ V` with
`‖ψ_0‖² + ‖ψ_1‖² = 1` and `‖ψ_0‖, ‖ψ_1‖ > 0`; write `|ψ⟩ = |ψ_0⟩|0⟩ + |ψ_1⟩|1⟩` and
`|ψ̄⟩ = (‖ψ_1‖/‖ψ_0‖)|ψ_0⟩|0⟩ − (‖ψ_0‖/‖ψ_1‖)|ψ_1⟩|1⟩`. Suppose a bidirectional canonical transducer
`R` with public space `V ⊗ ℂ²` acts as a reflection through `|ψ⟩`: `|ψ⟩ ⇝_R |ψ⟩` and
`|φ⟩ ⇝_R −|φ⟩` for all `|φ⟩ ⊥ |ψ⟩`. Then there are bidirectional canonical transducers `C` (public
space `V ⊗ ℂ²`) and `U` (public space `V`), the same for every input, with
1. `|ψ⟩ ⇝_C |ψ_1⟩|1⟩/‖ψ_1‖` with complexity at most `c (W(R,|ψ⟩) + ‖ψ_0‖² W(R,|ψ̄⟩))/‖ψ_1‖`;
2. `|ψ_1⟩/‖ψ_1‖ ⇝_U |ψ_1⟩/‖ψ_1‖` with complexity at most `c W(R,|ψ⟩)/‖ψ_1‖²`;
3. `|⊥⟩ ⇝_U −|⊥⟩` with complexity at most `c W(R, |⊥⟩|1⟩)` for all `|⊥⟩ ∈ V` with `⟨⊥|ψ_1⟩ = 0`.

**Formalization Note** The Hilbert spaces are finite-dimensional coordinate spaces (`V`, `H`, the
workspaces are finite types), the setting in which Definition 2.7's minimum exists (Theorem 2.8)
and in which Part II uses the corollary. The dependence of `ψ_0, ψ_1` on the implicit input is
explicit (proof, p.21), and `O(·)` is a universal constant `c` chosen before everything. -/
theorem corollary_3_4 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (V H W : Type) [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H] [Fintype W]
        [DecidableEq W] (D : Type) (O : D → Matrix.unitaryGroup H ℂ)
        (ψ0 ψ1 : D → EuclideanSpace ℂ V) (R : BiCanonical (V × Fin 2) H W),
        (∀ x, ‖ψ0 x‖ ^ 2 + ‖ψ1 x‖ ^ 2 = 1) → (∀ x, 0 < ‖ψ0 x‖) → (∀ x, 0 < ‖ψ1 x‖) →
        (∀ x, Transduces (R.apply (O x)) (ampState (ψ0 x) (ψ1 x)) (ampState (ψ0 x) (ψ1 x))) →
        (∀ x (φ : EuclideanSpace ℂ (V × Fin 2)), inner ℂ (ampState (ψ0 x) (ψ1 x)) φ = 0 →
          Transduces (R.apply (O x)) φ (-φ)) →
        ∃ (nC nU : ℕ) (C : BiCanonical (V × Fin 2) H (Fin nC)) (U : BiCanonical V H (Fin nU)),
          ∀ x,
            TransducesWithin (C.apply (O x)) (ampState (ψ0 x) (ψ1 x))
              (tensorVec (((‖ψ1 x‖ : ℝ) : ℂ)⁻¹ • ψ1 x) (ket 1))
              (c * (transductionComplexity (R.apply (O x)) (ampState (ψ0 x) (ψ1 x)) +
                  ‖ψ0 x‖ ^ 2 *
                    transductionComplexity (R.apply (O x)) (ampPerp (ψ0 x) (ψ1 x))) /
                ‖ψ1 x‖) ∧
            TransducesWithin (U.apply (O x)) ((((‖ψ1 x‖ : ℝ) : ℂ)⁻¹) • ψ1 x)
              ((((‖ψ1 x‖ : ℝ) : ℂ)⁻¹) • ψ1 x)
              (c * transductionComplexity (R.apply (O x)) (ampState (ψ0 x) (ψ1 x)) /
                ‖ψ1 x‖ ^ 2) ∧
            ∀ φ : EuclideanSpace ℂ V, inner ℂ φ (ψ1 x) = 0 →
              TransducesWithin (U.apply (O x)) φ (-φ)
                (c * transductionComplexity (R.apply (O x)) (tensorVec φ (ket 1))) := by sorry

end QVolTransducer
