-- Prove2me | Theorems.Thm_TDHamSim_QueryOptimal_lemma_6
-- name    : TDHamSim.QueryOptimal.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T14:23:16.001185+00:00
-- url     : https://prove2.me/theorems/3e5453b5-fcf4-4b1c-848d-7e4c3a5310bf
-- title:
--   Lemma 6 — lower-triangular private block
-- statement:
--   For $J=2^m$, $0<w\le1$ and any family of Hermitian unitary oracle blocks, the private block $A$ of the explicitly defined transducer satisfies
--
--   $$A=i(I-\Delta)\mathrm{HAM\!\text{-}\!T}.$$
--
--   The diagonal blocks of $\Delta$ are $(1-c)\Pi_{A,0}$, its lower blocks are $s^2c^{r-j-1}\Pi_{A,0}$ for $r>j$, and its upper blocks are zero. This statement isolates the temporal triangular structure independently of Hamiltonian interpolation data.
--
--   Differences from the source:
--   - encoding: qubit Hilbert spaces, tensor registers and time labels → binary-string bases, finite coordinate matrices and Fin indices with the spectral norm; reason: a change of coordinates representing every source instance, with explicit direct-sum and flag encodings
--   - generalization: the private block of the Hamiltonian transducer → the same identity for every Hermitian unitary block family and every 0<w≤1; reason: the block identity depends only on the update product, and specializing the blocks to Definition 3 gives the source
-- source:
--   Boyang Chen, Minbo Gao, Zhengfeng Ji, Tongyang Li, Xinzhao Wang, Shuo Zhou, STOC 2027 submission #383 (October 2026), Lemma 6 — lower-triangular private block, p.20. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/383.pdf

import Definitions.Def_TDHamSim_QueryOptimal_LCU

open scoped Matrix.Norms.L2Operator

namespace TDHamSim.QueryOptimal

/-- Lemma 6, p.20: the full lower-triangular private block. -/
theorem lemma_6 {n a : ℕ} (m : ℕ) (w : ℝ) (hw : 0 < w) (hw1 : w ≤ 1)
    (O : Fin (2^m) → Mat (Bits a × Bits n))
    (hO : ∀ j, (O j).IsHermitian ∧ IsUnitary (O j)) :
    privateBlock w O = Complex.I • ((1 - delta (2^m) a n w) * hamT O) := by sorry

end TDHamSim.QueryOptimal
