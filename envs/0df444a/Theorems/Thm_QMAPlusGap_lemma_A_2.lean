-- Prove2me | Theorems.Thm_QMAPlusGap_lemma_A_2
-- name    : QMAPlusGap.lemma_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:09:32.805567+00:00
-- url     : https://prove2.me/theorems/a4eb2795-9085-43d5-a665-1ec2f9b6bf92
-- title:
--   Lemma A.2 — $-\tfrac1mI\preceq T_P,T_Q\preceq I$ on $\mathrm{Sym}^m\otimes\mathrm{Sym}^m$
-- statement:
--   Let $P$ be an orthogonal projector on $\mathcal H$ and $Q=I-P$. On two copies of $\mathcal H^{\otimes m}$ let
--   $$
--   T_P=\frac1{m^2}\sum_{i,j=1}^{m}P^{(1)}_iP^{(2)}_jF_{ij},\qquad T_Q=\frac1{m^2}\sum_{i,j=1}^{m}Q^{(1)}_iQ^{(2)}_jF_{ij}.
--   $$
--   On $\mathrm{Sym}^m(\mathcal H)\otimes\mathrm{Sym}^m(\mathcal H)$ these operators commute and satisfy
--   $$
--   -\frac1mI\preceq T_P\preceq I,\qquad -\frac1mI\preceq T_Q\preceq I.\tag{A.3}
--   $$
--   Concretely: for every $\Psi\in\mathrm{Sym}^m(\mathcal H)\otimes\mathrm{Sym}^m(\mathcal H)$, the vectors $T_P\Psi$, $T_Q\Psi$ lie in the same space, $T_PT_Q\Psi=T_QT_P\Psi$, the expectations $\langle\Psi|T_P|\Psi\rangle$, $\langle\Psi|T_Q|\Psi\rangle$ are real, and both lie in $[-\|\Psi\|^2/m,\ \|\Psi\|^2]$.
--
--   Differences from the source:
--   - reading: on Sym^m(H) ⊗ Sym^m(H) the operators commute and −(1/m)I ⪯ T ⪯ I → for every Ψ in the range of P_sym ⊗ P_sym: T_PΨ, T_QΨ stay in it, T_P T_Q Ψ = T_Q T_P Ψ, ⟨Ψ|T|Ψ⟩ is real and lies in [−∥Ψ∥²/m, ∥Ψ∥²]; reason: the Loewner order of the compressions to an invariant subspace is exactly these quadratic-form conditions
--   - encoding: m ≥ 1 (implicit: positions in [m]) → no hypothesis on m; reason: at m = 0 Lean's 1/0 = 0 makes T_P = T_Q = 0 and every clause holds; no instance of the source changes
-- source:
--   Miyamoto, Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs, arXiv:2608.07986 (held version, sha256 4667925f…), Lemma A.2, p.32 (proof pp.33–34)

import Mathlib
import Definitions.Def_QMAPlusGap_symProj
import Definitions.Def_QMAPlusGap_IsOrthProj
import Definitions.Def_ArgmaxDeFinetti_vnorm
import Definitions.Def_QMAPlusGap_expect
import Definitions.Def_QMAPlusGap_swapAvg

set_option autoImplicit false

open scoped MatrixOrder ComplexOrder
open MeasureTheory Filter Matrix

namespace QMAPlusGap

/-- **Lemma A.2**, Miyamoto, *Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs*, arXiv:2608.07986 (held version, sha256 4667925f…), p.32: "Let P be an orthogonal projector on H, and set Q = I − P. On two copies of
Sym^m(H), define T_P = (1/m²) Σ_{i,j=1}^{m} P^{(1)}_i P^{(2)}_j F_{ij}, T_Q = (1/m²) Σ_{i,j=1}^{m} Q^{(1)}_i Q^{(2)}_j
F_{ij}, where F_{ij} swaps register i of the first copy with register j of the second copy. On
Sym^m(H) ⊗ Sym^m(H), these operators commute and satisfy −(1/m) I ⪯ T_P ⪯ I, −(1/m) I ⪯ T_Q ⪯ I. (A.3)"

For every `Ψ ∈ Sym^m(H) ⊗ Sym^m(H)`: `T_P Ψ` and `T_Q Ψ` lie in `Sym^m(H) ⊗ Sym^m(H)` (the operators act on
this space), `T_P T_Q Ψ = T_Q T_P Ψ`, the expectations `⟨Ψ|T_P|Ψ⟩`, `⟨Ψ|T_Q|Ψ⟩` are real, and
`−(1/m)∥Ψ∥² ≤ ⟨Ψ|T|Ψ⟩ ≤ ∥Ψ∥²` for `T ∈ {T_P, T_Q}`.

**Formalization Note** `Sym^m(H) ⊗ Sym^m(H)` is the range of `P_sym^{(m)} ⊗ P_sym^{(m)}` (Kronecker product);
the Loewner order of the compressions is stated through quadratic forms (real, with the two bounds); `∥·∥` is the
Euclidean norm. -/
theorem lemma_A_2 {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℕ) (P : Matrix ι ι ℂ) (hP : IsOrthProj P)
    (Ψ : (Fin m → ι) × (Fin m → ι) → ℂ)
    (hΨ : Matrix.kroneckerMap (· * ·) (symProj (ι := ι) m) (symProj m) *ᵥ Ψ = Ψ) :
    Matrix.kroneckerMap (· * ·) (symProj (ι := ι) m) (symProj m) *ᵥ (swapAvg m P *ᵥ Ψ) = swapAvg m P *ᵥ Ψ ∧
    Matrix.kroneckerMap (· * ·) (symProj (ι := ι) m) (symProj m) *ᵥ (swapAvg m (1 - P) *ᵥ Ψ) =
      swapAvg m (1 - P) *ᵥ Ψ ∧
    swapAvg m P *ᵥ (swapAvg m (1 - P) *ᵥ Ψ) = swapAvg m (1 - P) *ᵥ (swapAvg m P *ᵥ Ψ) ∧
    (expect (swapAvg m P) Ψ).im = 0 ∧ (expect (swapAvg m (1 - P)) Ψ).im = 0 ∧
    -(1 / (m : ℝ)) * ArgmaxDeFinetti.vnorm Ψ ^ 2 ≤ (expect (swapAvg m P) Ψ).re ∧
    (expect (swapAvg m P) Ψ).re ≤ ArgmaxDeFinetti.vnorm Ψ ^ 2 ∧
    -(1 / (m : ℝ)) * ArgmaxDeFinetti.vnorm Ψ ^ 2 ≤ (expect (swapAvg m (1 - P)) Ψ).re ∧
    (expect (swapAvg m (1 - P)) Ψ).re ≤ ArgmaxDeFinetti.vnorm Ψ ^ 2 := by sorry

end QMAPlusGap
