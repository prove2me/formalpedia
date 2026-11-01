-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P03_garbage_coherence
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P03.garbage_coherence
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T03:58:54.669002+00:00
-- url     : https://prove2.me/theorems/f99581d1-5b75-4d92-821c-a447757d806b
-- title:
--   §2.4.5: garbage trace and loss of coherence
-- statement:
--   Let a reversible computation send basis input $x$ with zero work to $(G(x),g(x))$, and let $|\xi\rangle=\sum_x c_x|x\rangle$ be normalized. The physical basis map is injective. After discarding the work,
--
--   $$
--   \rho=\sum_{x,y:g(x)=g(y)}c_x\overline{c_y}|G(x)\rangle\langle G(y)|.
--   $$
--
--   If the garbage is input-independent, this is the pure density of $\sum_x c_x|G(x)\rangle$. If $g$ is injective, it is the diagonal mixture $\sum_x|c_x|^2|G(x)\rangle\langle G(x)|$.
--
--   The coefficient order corrects the printed conjugation error using density definition (8). Input-independent garbage suffices to preserve coherence; it need not literally be zero.
-- source:
--   Quantum measurements and the Abelian Stabilizer Problem, arXiv:quant-ph/9511026v1, PDF p. 15, §2.4.5: garbage trace and loss of coherence

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P03

noncomputable section

open scoped Matrix ComplexConjugate Kronecker

namespace QAlgorithms.Papers.Independent.Intakethird100.P03

open QAlgorithms.Papers.Independent.Renew46.P01 (cleanVector)

attribute [local instance] Classical.propDecidable

/-- PDF pp.14–15: reduced density, constant-garbage coherence, and injective-garbage
classical mixture. Source correction: printed conj(c_x)c_y is replaced by c_x conj(c_y),
as required by density definition (8). The correction was independently checked in round 1. -/
theorem garbage_coherence {n w : ℕ} (G : Qubits n → Qubits n)
    (g : Qubits n → Qubits w) (c : EuclideanSpace ℂ (Qubits n))
    (hc : IsState c) (hphysical : Function.Injective (fun x => (G x, g x))) :
    traceRight (pureDensity (garbageState G g c)) =
      (∑ x, ∑ y, if g x = g y then
        (c x * conj (c y)) • (fun i j => (ket (G x)) i * conj ((ket (G y)) j)) else 0) ∧
    ((∃ z, ∀ x, g x = z) →
      traceRight (pureDensity (garbageState G g c)) = pureDensity (coherentImage G c)) ∧
    (Function.Injective g → traceRight (pureDensity (garbageState G g c)) =
      ∑ x, (‖c x‖ ^ 2 : ℂ) • pureDensity (ket (G x))) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P03

end
