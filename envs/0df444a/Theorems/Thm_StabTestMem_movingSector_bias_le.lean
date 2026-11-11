-- Prove2me | Theorems.Thm_StabTestMem_movingSector_bias_le
-- name    : StabTestMem.movingSector_bias_le
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:13:24.266438+00:00
-- url     : https://prove2.me/theorems/6b0936fb-66f8-4fe0-8196-27ff471b3497
-- title:
--   Lemma 5.8 — the moving sector $M_t$ contributes little
-- statement:
--   Let $t<n$. For every adaptive protocol with $k$ qubits of memory that uses $t$ single copies of an $n$-qubit state, with transcript operators $E_x$ (Lemma 3.10),
--
--   $$\frac1{2^{nt}}\sum_x\Big|\sum_{O\in M_t}\operatorname{Tr}[R(O)E_x]\Big|\le2^{1-(n-k-7t)/2}, \tag{105}$$
--
--   where $M_t=\mathcal O_t\setminus\mathcal O_{t-1}$ is the set of $O\in\mathcal O_t$ that move $e_1$.
--
--   This is the main technical lemma of the lower bound; applied recursively it bounds the likelihood ratio of Theorem 5.9.
--
--   Differences from the source:
--   - encoding: Definition 3.7: instruments in rounds 1, …, t−1 and a final POVM; adaptive single-copy protocol with a k-qubit memory → an instrument in every round (the last one's output memory discarded), a deterministic decision on the transcript, a finite outcome type; reason: a POVM {E^x} is the instrument Y ↦ Tr(E^x Y)η_*; randomness is absorbed into outcomes
--   - encoding: Tr[R(O)E_x], P_mm(x) = Tr[E_x]/2^{nt}, L(x) → the transcript functional P.weight evaluated at R(O), ρ_mm, σ (avgDev); reason: Lemma 3.10's E_x extended linearly to every t-copy operator
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), Lemma 5.8, Eq. (105), p. 42

import Definitions.Def_StabTestMem_MemProtocol
import Definitions.Def_StabTestMem_InMt
import Definitions.Def_StabTestMem_ROp

namespace StabTestMem

open QAlgorithms

open Classical in
/-- **Lemma 5.8: the moving sector `M_t` contributes little.** Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), Lemma 5.8, p. 42: "Let t < n.
For any protocol using single-copy measurement and k qubits of memory, it holds that
(1/2^{nt}) Σ_x |Σ_{O∈M_t} Tr[R(O)E_x]| ≤ 2^{1−(n−k−7t)/2}. (105)"

For every adaptive protocol with `k` qubits of memory and `t < n` single copies of an `n`-qubit
state, with `Tr[R(O)E_x]` the transcript functional evaluated at `R(O)`.

**Formalization Note.** `Tr[R(O)E_x]` is `P.weight (ROp O) x` (Lemma 3.10's `E_x`, extended
linearly); `M_t` is `InMt`. The exponent is a real power; `k` may exceed `n`. -/
theorem movingSector_bias_le {n k t : ℕ} {X : Type} [Fintype X] (P : MemProtocol n k t X)
    (ht : t < n) :
    ((2 : ℝ) ^ (n * t))⁻¹ *
        ∑ x, ‖∑ O ∈ Finset.univ.filter (fun O : Matrix (Fin t) (Fin t) (ZMod 2) => InMt O),
          P.weight (ROp O) x‖ ≤
      (2 : ℝ) ^ (1 - ((n : ℝ) - k - 7 * t) / 2) := by sorry

end StabTestMem
