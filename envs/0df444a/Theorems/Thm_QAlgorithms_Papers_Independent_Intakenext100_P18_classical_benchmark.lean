-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P18_classical_benchmark
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P18.classical_benchmark
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:29:06.699133+00:00
-- url     : https://prove2.me/theorems/534c0388-35e3-463a-8e3a-fa61ac1d008f
-- title:
--   Exact optimal classical teleportation fidelity
-- statement:
--   Let $d\ge1$ and use the normalized uniform Haar distribution of pure $d$-dimensional inputs. For any finite POVM $(M_i)_{i=1}^k$ with $M_i\succeq0$ and $\sum_iM_i=I$, and any density operators $\tau_i$, the classical measure-and-prepare channel is $C(X)=\sum_i\operatorname{Tr}(M_iX)\tau_i$. Its average squared survival fidelity obeys
--
--   $$f(C)\le\frac2{d+1}.$$
--
--   The channel $C_0(X)=\sum_{i=0}^{d-1}X_{ii}|i\rangle\langle i|$, implemented by computational-basis measurement, classical communication and preparation of the reported basis state, attains equality. Equivalently, every separable bipartite density operator has fixed plus overlap at most $1/d$, and some separable density attains $1/d$.
--
--   Thus $2/(d+1)$ is the achieved classical optimum. The statement includes explicit membership of $C_0$ in the measure-and-prepare class and does not rely on a default-valued real supremum.
-- source:
--   General teleportation channel, singlet fraction and quasi-distillation, arXiv:quant-ph/9807091v2, PDF p. 8, §IV, unnumbered: optimal purely classical teleportation fidelity

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P18

noncomputable section

open QAlgorithms MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Intakenext100.P18

open QAlgorithms.Papers.Independent.Claimed50.P28 (maximallyEntangledDensity)

open QAlgorithms.Papers.Independent.Support50.P11 (choiState teleportWeyl bellKet)

open QAlgorithms.Papers.Independent.Renew46.P40 (initialJoint)

/-- PDF p.8, section IV: optimal purely classical fidelity, with a named
achiever as well as the upper bound against every measure/prepare channel.
The equivalent singlet bound is stated for every separable density. -/
theorem classical_benchmark (d : ℕ) (hd : 0 < d) :
    letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩;
    (∀ k : ℕ, ∀ M tau : Fin k → Matrix (Fin d) (Fin d) ℂ,
      IsPOVM M → (∀ i, IsDensityMatrix (tau i)) →
      QuditFidelity.averageFidelity d hd ((fun X => ∑ i, (M i * X).trace • tau i)) ≤ 2 / (d + 1 : ℝ)) ∧
    (∃ k : ℕ, ∃ M tau : Fin k → Matrix (Fin d) (Fin d) ℂ,
      IsPOVM M ∧ (∀ i, IsDensityMatrix (tau i)) ∧ (fun X => ∑ i, (M i * X).trace • tau i) = basisClassical d) ∧
    IsChannel (basisClassical d) ∧
    QuditFidelity.averageFidelity d hd (basisClassical d) = 2 / (d + 1 : ℝ) ∧
    (∀ rho : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,
        Entanglement.IsSeparableDensity rho → effectProb (maximallyEntangledDensity d) rho ≤ 1 / (d : ℝ)) ∧
    (∃ rho : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,
      Entanglement.IsSeparableDensity rho ∧ effectProb (maximallyEntangledDensity d) rho = 1 / (d : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P18

end
