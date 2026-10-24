-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P42_schmidt_coding
-- name    : QAlgorithms.Papers.Independent.Support50.P42.schmidt_coding
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:21:09.392094+00:00
-- url     : https://prove2.me/theorems/5355fc68-deff-402e-8c4c-379a2c786c11
-- title:
--   Schmidt coding erases complementary inputs and cannot be faithful
-- statement:
--   For $p\in(0,1)$, source $Q'$ emits $\sqrt{1-p}|0\rangle+(-1)^b\sqrt p|1\rangle$ with uniform bit $b$. Let $|\Psi_x\rangle$ be its length-$n$ product signal, with $n>2$ as in the section, for uniform binary label $x$, and let $\bar x$ be its complement. The Schmidt encoder measures the weight $k$ and retains both the quantum branch and the classical outcome. Then
--
--   $$\mathcal E_n(|\Psi_x\rangle\langle\Psi_x|)=\mathcal E_n(|\Psi_{\bar x}\rangle\langle\Psi_{\bar x}|),\qquad F_n(\mathcal D)\le\frac{1+|1-2p|^n}{2}$$
--
--   for every decoder channel $\mathcal D$ independent of $x$, where $F_n$ is source-average squared fidelity. Bare transmission which forgets $k$ without decoding has average fidelity tending to zero. The displayed bound prevents arbitrary decoders, even using $k$, from attaining asymptotically perfect fidelity.
-- source:
--   Concentrating Partial Entanglement by Local Operations, arXiv:quant-ph/9511030v1, PDF p. 13, §IV: Schmidt coding erases complements and cannot be faithful

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P42

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P42

open scoped BigOperators Matrix ComplexConjugate

open MeasureTheory ProbabilityTheory

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the exact accepted objects, without introducing same-name aliases.

open Information100.P21 (Op Vec FiniteLOCC)

open Dependency50.P42 (dimensionedPower singlets)

open Dependency50.P48 (pureFidelity)

open Gap48.P32 (pairOfState)

open Next46.P39 (rectAct)

/-- PDF pp.13--14: complement erasure even with the classical outcome,
bare-fidelity limit zero, and a uniform bound for every decoder channel.
The decoder receives the entire classical-quantum output, never the unknown x. -/
theorem schmidt_coding (p : ℝ) (hp : 0<p) (hp1 : p<1) :
    (∀ (n : ℕ), 2<n → ∀ x : Fin n → Bool,
      flaggedEncoder n (pureDensity (sourceKet p x))=
        flaggedEncoder n (pureDensity (sourceKet p (fun i => !(x i))))) ∧
    (∀ (n : ℕ) (D : Superop (Fin (n+1) × (Fin n → Bool)) (Fin n → Bool)),
      2<n → IsChannel D → codingFidelity n p D≤(1+|1-2*p|^n)/2) ∧
    Filter.Tendsto (fun n : ℕ => ((2 : ℝ)^(n+3))⁻¹*∑ x : Fin (n+3) → Bool,
      pureFidelity (sourceKet p x) (bareEncoder (n+3) (pureDensity (sourceKet p x))))
      Filter.atTop (nhds (0 : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P42

end
