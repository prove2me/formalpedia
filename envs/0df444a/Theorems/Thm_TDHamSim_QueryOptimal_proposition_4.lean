-- Prove2me | Theorems.Thm_TDHamSim_QueryOptimal_proposition_4
-- name    : TDHamSim.QueryOptimal.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T14:22:46.623+00:00
-- url     : https://prove2.me/theorems/d45c287d-284a-46a2-beb4-f010cb5731f2
-- title:
--   Proposition 4 — one-query Cayley transducer
-- statement:
--   For $n$ system qubits, $a$ oracle ancillas, $J=2^m$, $\alpha>0$, $\beta\ge0$, $T>0$ and $w=\alpha T/J\le1$, there is a standard circuit, chosen independently of $H$ and its oracle blocks, that implements $S$ using exactly one controlled HAM-T query. For every admissible $H$ and oracle,
--
--   $$\|\Gamma\|^2\le\alpha T,\qquad S(\psi\oplus\Gamma\psi)=U_C\psi\oplus\Gamma\psi\quad\text{for every }\psi.$$
--
--   The implementation returns temporary work wires exactly to zero. No gate bound is imposed at this milestone.
--
--   Differences from the source:
--   - encoding: qubit Hilbert spaces, tensor registers and time labels → binary-string bases, finite coordinate matrices and Fin indices with the spectral norm; reason: a change of coordinates representing every source instance, with explicit direct-sum and flag encodings
--   - generalization: the circuit S implemented with the HAM-T oracle of Definition 3 → the same one-query circuit implements S for every oracle block family O_0,…,O_{J−1} (no Hermiticity, unitarity or compression condition); reason: S = S°(I ⊕ HAM-T) with S° oracle-independent, so the circuit identity is linear in the blocks; restricting to Definition 3 blocks gives the source
-- source:
--   Boyang Chen, Minbo Gao, Zhengfeng Ji, Tongyang Li, Xinzhao Wang, Shuo Zhou, STOC 2027 submission #383 (October 2026), Proposition 4 — one-query Cayley transducer, p.16. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/383.pdf

import Definitions.Def_TDHamSim_QueryOptimal_LCU

open scoped Matrix.Norms.L2Operator

namespace TDHamSim.QueryOptimal

/-- Proposition 4, p.16: a fixed one-query circuit, catalyst norm, and transducer identity. -/
theorem proposition_4 (n a m : ℕ) (α β T : ℝ)
    (hα : 0 < α) (hβ : 0 ≤ β) (hT : 0 < T) (hw : stepWeight α T (2^m) ≤ 1) :
    ∃ k : ℕ, ∃ c : ConstDepthUnitary.OCircuit (Wires (1+m+a+n) k) (1+m+a+n),
      c.IsStandard ∧ c.queries = 1 ∧
      (∀ O : Fin (2^m) → Mat (Bits a × Bits n),
        Implements c (controlledHAMT O) (physical m a n (transducer (stepWeight α T (2^m)) O))) ∧
      ∀ (H : ℝ → Mat (Bits n)) (O : Fin (2^m) → Mat (Bits a × Bits n)),
        IsHamiltonian H α β T → IsHAMT H α T O →
        opNorm (gamma H α T O)^2 ≤ α*T ∧ ∀ v : Ket (Bits n),
          act (transducer (stepWeight α T (2^m)) O) (join v (act (gamma H α T O) v)) =
            join (act (cayleyProduct H α T (2^m)) v) (act (gamma H α T O) v) := by sorry

end TDHamSim.QueryOptimal
