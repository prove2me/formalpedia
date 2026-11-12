-- Prove2me | Theorems.Thm_QuantumGroupCodes836_Addressability_addressable_code_families
-- name    : QuantumGroupCodes836.Addressability.addressable_code_families
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T17:12:45.860413+00:00
-- url     : https://prove2.me/theorems/5934f04e-75bf-4470-b614-7aef25286069
-- title:
--   Theorem 1.1 / 4.8 — addressable quantum group-code families
-- statement:
--   For every power of two $t>4$, let $q=t^4$. For every integer $1<m\le t/2-1$, there exist both of the following growing families over the same field of $q$ elements:
--
--   $$[[n,\Theta(n/\log n),\Theta(n)]]_q\quad\text{regular quantum group codes},$$
--   $$[[n,\Theta(n),\Theta(n)]]_q\quad\text{free quantum group codes}.$$
--
--   For every $1<a\le m$, the regular family has fully addressable transversal $C^{a-1}Z$ gates and every weighted logical circuit of these gates on the fixed $m$ blocks, each gate using $a$ distinct blocks, admits physical depth $O(k^{a-1})$ uniformly over the circuit. The free family has a global transversal $C^aZ$ gate and orbit-wise addressable $C^{a-1}Z$ gates across $\Theta(\log n)$ orbits, all of size $\Theta(n/\log n)$, including simultaneous shared-shift products.
--
--   Both families have operational Las Vegas decoders for X and Z errors of positive linear radius, with expected charged cost $O(n^2(\log n)^4)$. Every asymptotic witness is chosen before the family index, circuit and adversarial error; one family supports every required arity. The source regular/free refinements and every headline clause are retained.
--
--   Differences from the source:
--   - encoding: CSS codes and module-linear sections → actual normalized coset subspaces and equivariant linear sections of actual quotients; reason: these are equivalent finite-coordinate models, with computed logical dimension and quotient-weight distance
--   - reading: Las Vegas decoding with polylogarithmic time → almost-sure termination, correctness of every terminating run and expected charged cost with log exponent four; reason: footnotes 3 and 7 fix the exponent; a finite-field RAM consumes independent uniform symbols and counts every operation and output read
--   - generalization: the prose uses m blocks while the display uses a participating blocks → circuits on all fixed m blocks, with each gate on any a distinct blocks; reason: this includes the displayed a-block case and the prose m-block case; a constant depending only on fixed m covers all participating block choices
--   - reading: a transversal C^{m̃}Z gate, (C^{m̃}Z)^{⊗n_Q} = (C^{m̃}Z)^{⊗k_Q} → for every γ ∈ F_q, one aligned layer of physical C^{m̃}Z gates on all physical sites, with site weights γ·u_j, implements the logical C^{m̃}Z_γ on every logical qudit; reason: p.10 defines a transversal logical gate as one realized by a depth-one circuit of physical C^{m−1}Z_γ gates; the logical action is the source uniform one, and γ = 1 recovers the displayed gate
-- source:
--   Virgile Guemard, Jean Gasnier, STOC 2027 submission #836 (October 2026), Theorem 1.1, restated as Theorem 4.8, p.3; restatement p.18, proof pp.18–19; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/836.pdf

import Definitions.Def_QuantumGroupCodes836_Addressability_Families

set_option autoImplicit false

namespace QuantumGroupCodes836.Addressability

theorem addressable_code_families (t m : ℕ)
    (ht : ∃ s : ℕ, t = 2 ^ s) (ht4 : 4 < t)
    (hm : 1 < m) (hmt : m ≤ t / 2 - 1) :
    ∃ A : QuantumAlphabet (t ^ 4),
      ∃ regular free : ℕ → GroupCode A.carrier,
        RegularFamily m regular ∧ FreeFamily m free := by sorry

end QuantumGroupCodes836.Addressability
