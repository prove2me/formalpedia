-- Prove2me | Theorems.Thm_ParityCubes_Supplement_theorem_I_1
-- name    : ParityCubes.Supplement.theorem_I_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:17:25.712297+00:00
-- url     : https://prove2.me/theorems/5ba80973-386e-4759-bb7b-dfe77218b921
-- title:
--   Theorem I.1 — $\mathrm{cert}$ and $\zeta$ of ordered matrix branching programs in $n\,2^{O(w^2)}$ time
-- statement:
--   Let $f(x)=u^{\mathsf T}\prod_{i=1}^{n}(A_i+x_iB_i)\,v$ over $\mathbb F_2$, with matrices of dimension at most $w$ and each variable appearing in one layer. Then one can compute $\mathrm{cert}(f)$ together with a minimizing certificate, or report infeasibility, in time $n\,2^{O(w^2)}$. The same bound holds for $\zeta(f)$ and a minimizing zero cube.
--
--   The fixed variable order makes the problem linear in the number of layers, in contrast to the doubly exponential dependence on treewidth.
--
--   **Formalization Note.** Time is counted on a deterministic unit-cost word RAM with $\Theta(\log\ell)$-bit words.
--
--   Differences from the source:
--   - reading: time n·2^{O(w²)} (no machine model named; unit cost per operation on rows, spaces and cost counters) → steps of the published deterministic unit-cost word RAM TrulySubcubicAPSP, correct for every word size W ≥ b(⌊log₂ ℓ⌋ + (w+1)² + 1), ℓ the number of input words; bound K(n+1)·2^{K(w+1)²}; reason: the paper's dynamic program stores 2^{O(w²)} states with random access, which needs words of Θ(log ℓ + w²) bits (logarithmic in the running time, the usual transdichotomous assumption); with Θ(log ℓ)-bit words those states cannot be addressed once w² ≫ log ℓ; n+1 and w+1 only cover n = 0, w = 0
--   - encoding: f given by u, A_i, B_i, v → lists of bits with dimensions d_0, …, d_n, all at most w; input words n, dims, u, A, B, v; reason: an explicit representation of the same inputs
--   - encoding: "compute cert(f) and a minimizing certificate, or report infeasibility" → the program rejects exactly when the optimum is +∞, otherwise accepts and writes the optimum and the indicator of a minimizing set after the input (OBPSolves); reason: an output convention
-- source:
--   Sheshadri, Smirnov, The Complexity of Choosing Parity Projections, arXiv:2611.00289 (manuscript sha256 95994d2d…), Theorem I.1, p.35 (PDF p.36); proof pp.35–36 (PDF pp.36–37)

import Mathlib
import Definitions.Def_ParityCubes_cubeSum
import Definitions.Def_TrulySubcubicAPSP_WordRAM
import Definitions.Def_ParityCubes_Supplement_OBP

set_option autoImplicit false

namespace ParityCubes.Supplement

open ParityCubes

/-- **Theorem I.1** (Sheshadri–Smirnov, *The Complexity of Choosing Parity Projections*,
arXiv:2611.00289, manuscript sha256 95994d2d…, Theorem I.1, p.35 (PDF p.36)). Given
`f(x) = uᵀ ∏_{i=1}^{n} (A_i + x_i B_i) v` over `𝔽₂`, with matrices of dimension at most `w` and each
variable appearing in one layer, one can compute `cert(f)` and a minimizing certificate, or report
infeasibility, in time `n·2^{O(w²)}`. The same bound holds for `ζ(f)`.

**Formalization Note.** The model is the published deterministic unit-cost word RAM
`TrulySubcubicAPSP` (one step per instruction) with words of `Θ(log ℓ + w²)` bits, i.e. logarithmic
in the running time (the usual transdichotomous assumption: a word holds an address of the memory
used, here the `2^{O(w²)}` states of the dynamic program of the proof, p.36 (PDF p.37)): the programs
work for every word size `W ≥ b(⌊log₂ ℓ⌋ + (w+1)² + 1)`, `ℓ` the number of input words. With words of
only `Θ(log ℓ)` bits the `2^{O(w²)}` states could not be addressed once `w² ≫ log ℓ`. `n·2^{O(w²)}` is
`K(n+1)·2^{K(w+1)²}`, one `K` for all programs. Output conventions are those of `OBPSolves`. -/
theorem theorem_I_1 :
    ∃ (P Pz : List TrulySubcubicAPSP.Instr) (b K : ℕ),
      ∀ (Q : OBP) (w : ℕ), Q.WF → (∀ d ∈ Q.dims, d ≤ w) →
        ∀ W : ℕ, b * (Nat.log2 Q.words.length + (w + 1) ^ 2 + 1) ≤ W →
          OBPSolves P Q W (K * (Q.n + 1) * 2 ^ (K * (w + 1) ^ 2))
              (fun S => IsCertificate Q.eval S) (cert Q.eval) ∧
          OBPSolves Pz Q W (K * (Q.n + 1) * 2 ^ (K * (w + 1) ^ 2))
              (fun S => IsZeroCube Q.eval S) (zeta Q.eval) := by sorry

end ParityCubes.Supplement
