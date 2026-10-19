-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P04_noAutomaticTensorization
-- name    : QAlgorithms.Papers.Independent.Information100.P04.noAutomaticTensorization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:33:09.528769+00:00
-- url     : https://prove2.me/theorems/1df8791f-0174-4039-afb8-b1958affd78c
-- title:
--   Explicit failure of one-copy quadratic-control tensorization
-- statement:
--   On a qubit with trivial second party and no ancillary system, define $\mathcal K(X)=\tfrac32X-\tfrac12\operatorname{Tr}(X)I$. This map is self-adjoint and strictly positive for the Hilbert–Schmidt inner product, has eigenvalue $1/2$ on the identity, and has eigenvalue $3/2$ on every traceless operator. Every qubit effect $0\le Q\le I$ satisfies
--
--   $$\langle Q,\mathcal K(Q)\rangle\le\|Q\|_\infty^2.$$
--
--   However, the Bell projection $\Phi_2$ on two qubits is an effect of norm one and satisfies $\langle\Phi_2,\mathcal K^{\otimes2}(\Phi_2)\rangle=7/4>1=\|\Phi_2\|_\infty^2$. Partial transpose on the trivial second party is the identity. Thus strict Hilbert–Schmidt positivity and one-copy control of every effect do not entail control on every tensor power.
-- source:
--   On PPT entanglement distillation, arXiv:2610.12454v1, PDF p. 20, eq84-86

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P04

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

namespace QAlgorithms.Papers.Independent.Information100.P04

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Eqs.(84)–(86), PDF p.20: an explicit strictly positive one-copy form that fails on two
copies. The second party is trivial, so its partial transpose is the identity. -/
theorem noAutomaticTensorization :
    (∀ X Y : Matrix Bool Bool ℂ, (Xᴴ * qubitK Y).trace = ((qubitK X)ᴴ * Y).trace) ∧
    (∀ X : Matrix Bool Bool ℂ, X ≠ 0 → 0 < hsQuadratic qubitK X) ∧
    qubitK 1 = (1/2:ℂ) • (1:Matrix Bool Bool ℂ) ∧
    (∀ X : Matrix Bool Bool ℂ, X.trace = 0 → qubitK X = (3/2:ℂ) • X) ∧
    (∀ Q : Matrix Bool Bool ℂ, IsEffect Q → hsQuadratic qubitK Q ≤ (specNorm Q)^2) ∧
    IsEffect bellTwo ∧ specNorm bellTwo = 1 ∧
    hsQuadratic (piSuperop (fun _ : Fin 2 => qubitK)) bellTwo = 7/4 ∧
    (specNorm bellTwo)^2 < hsQuadratic (piSuperop (fun _ : Fin 2 => qubitK)) bellTwo := by sorry

end QAlgorithms.Papers.Independent.Information100.P04

end
