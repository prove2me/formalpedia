-- Prove2me | Theorems.Thm_TolProdTest_Supplement_theorem_4_1
-- name    : TolProdTest.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:09:06.803559+00:00
-- url     : https://prove2.me/theorems/bc799bcd-9ab9-4f27-90bb-9a961a59285c
-- title:
--   Theorem 4.1 — FPT closest product-state learner: $2^{\tilde O(\varepsilon^{-8})}(nd)^2\mathrm{poly}\log(nd/\delta)$ copies, $2^{\tilde O(\varepsilon^{-8})}n^3d^2\mathrm{poly}\log(nd/\delta)$ gates
-- statement:
--   Let $n\ge1$, $d\ge2$ and $\varepsilon,\delta\in(0,1/2)$. There is a quantum algorithm which, given independent copies of an unknown mixed state $\rho\in\mathcal D((\mathbb C^d)^{\otimes n})$, outputs with probability at least $1-\delta$ a classical description of a pure product state $|\hat u\rangle=|u_1\rangle\otimes\cdots\otimes|u_n\rangle$ such that
--
--   $$
--   \langle\hat u|\rho|\hat u\rangle\ \ge\ F_{\mathrm{prod}}(\rho)-\varepsilon ,
--   $$
--
--   using $2^{\tilde O(\varepsilon^{-8})}(nd)^2\,\mathrm{poly}(\log(nd/\delta))$ copies of $\rho$ and computational complexity $2^{\tilde O(\varepsilon^{-8})}n^3d^2\,\mathrm{poly}(\log(nd/\delta))$.
--
--   Precisely: there is an absolute constant $C>0$ such that for all such $\varepsilon,\delta,n,d$ there is a circuit over $\{H,S,T,X,\mathrm{CNOT}\}$, fixed before $\rho$, acting on $N$ encoded copies of $\rho$ and ancillas, with
--
--   $$
--   N\le 2^{C\varepsilon^{-8}\log(e/\varepsilon)^C}(nd)^2\log(nd/\delta)^C,\qquad \#\text{gates}\le 2^{C\varepsilon^{-8}\log(e/\varepsilon)^C}n^3d^2\log(nd/\delta)^C,
--   $$
--
--   whose measured output decodes to such a $|\hat u\rangle$ with probability at least $1-\delta$, for **every** density operator $\rho$ (no promise).
--
--   This is the paper's second main result (stated informally as Theorem 1.2): agnostic learning of the closest product state with the exponential dependence on $1/\varepsilon$ confined to a prefactor and a fixed polynomial degree in $n$ and $d$.
--
--   **Formalization Note** The algorithm model is the published goal's: a gate list over `ShiShallow.Instr` on $\rho^{\otimes N}$ encoded qudit by qudit, ancillas in $|0\rangle$, intermediate measurements and classical post-processing deferred into the circuit. All wires are measured and the output state is read by a fixed decoder (sign and $p$-bit fixed point for the real and imaginary parts of each amplitude, then per-site normalization); the algorithm chooses only the precision $p$ and the output wires.
--
--   Differences from the source:
--   - encoding: a quantum algorithm (no model named) → a gate list over ShiShallow.Instr {H,S,T,X,CNOT} on ρ^{⊗N} encoded qudit by qudit (Nat.clog 2 d wires per qudit, little-endian, copy-major) plus m ancillas in |0⟩, intermediate measurements and classical post-processing deferred into the circuit, fixed before ρ; sample complexity = N, computational complexity = number of gates; reason: the published goal's model (TolProdTest.theorem_1_1, paper.md decision 3); a fixed finite universal gate set matches any other up to the polylogarithmic factors already allowed (Solovay–Kitaev)
--   - encoding: outputs a classical description of a pure product state |û⟩ → every wire is measured and |û⟩ = prodVec (decodeProd p o y): sign plus p-bit fixed point for the real and imaginary part of each amplitude on wires chosen by an injective map o, then per-site normalization (zero ↦ |0⟩); the algorithm chooses p and o only; reason: a classical description is a bit string; finite-precision amplitudes reach every direction up to arbitrarily small error, and the decoder is fixed so no unbounded computation is hidden outside the gate count
--   - encoding: 2^{Õ(ε^{−8})}(nd)^2 poly(log(nd/δ)) copies and 2^{Õ(ε^{−8})} n^3 d^2 poly(log(nd/δ)) computational complexity → one absolute C > 0 chosen before ε, δ, n, d with N ≤ 2^{C ε^{−8} log(e/ε)^C} (nd)^2 log(nd/δ)^C and gates ≤ 2^{C ε^{−8} log(e/ε)^C} n^3 d^2 log(nd/δ)^C; reason: Õ suppresses polylogarithmic factors (p.8) and poly is a polynomial; log(e/ε) ≥ 1 is log(1/ε) up to C for ε < 1/2; log(nd/δ) > 1; a constant factor is absorbed in 2^{Cε^{−8}}; same reading as the published goal
-- source:
--   Bao, Helsen, Nguyen, Fully tolerant product state testing and closest product state learning, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), Theorem 4.1, eq. (80), p.19 (= Theorem 1.2, p.3; proof pp.19–39)

import Mathlib
import Definitions.Def_TolProdTest_fprod
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_TolProdTest_Supplement_learnSuccess

set_option autoImplicit false

open Matrix

namespace TolProdTest.Supplement

/-- **Theorem 4.1 (An FPT Closest Product State Learner)**, Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), p.19 (= Theorem 1.2, p.3): "Given n ≥ 1, d ≥ 2,
ε, δ ∈ (0, 1/2), the independent copies of an unknown mixed state ρ ∈ D((C^d)^{⊗n}), there is a quantum algorithm
which, with probability at least 1 − δ, outputs a classical description of a pure product state |û⟩, such that
⟨û|ρ|û⟩ ≥ F_prod(ρ) − ε, (80) with sample complexity 2^{Õ(ε^{−8})}(nd)^2 poly(log(nd/δ)) and computational
complexity 2^{Õ(ε^{−8})} n^3 d^2 poly(log(nd/δ))."

There is an absolute constant `C > 0` such that for all `ε, δ ∈ (0, 1/2)`, `n ≥ 1`, `d ≥ 2` there is a circuit
over `{H, S, T, X, CNOT}` on `N` encoded copies of `ρ` and `m` ancillas, with a precision `p` and an output wire
map `o`, all fixed before `ρ`, with `N ≤ 2^{C ε^{−8} log(e/ε)^C} (nd)^2 log(nd/δ)^C` and at most
`2^{C ε^{−8} log(e/ε)^C} n^3 d^2 log(nd/δ)^C` gates, such that for **every** density operator `ρ` the decoded pure
product state `|û⟩` satisfies `⟨û|ρ|û⟩ ≥ F_prod(ρ) − ε` with probability at least `1 − δ`.

**Formalization Note** The algorithm model is the published goal's (`TolProdTest.theorem_1_1`): a gate list over
`ShiShallow.Instr` acting on `ρ^{⊗N}` encoded qudit by qudit (`Nat.clog 2 d` wires per qudit, little-endian,
copy-major) and `m` ancillas in `|0⟩`; sample complexity is `N`, computational complexity the number of gates;
the circuit may depend on `(ε, δ, n, d)` but not on `ρ`. All wires are measured and the output state is read by
the fixed decoder `decodeProd` (sign plus `p`-bit fixed point per real and imaginary part of each amplitude,
then per-site normalization); the algorithm chooses only `p` and the wire map. `Õ` and `poly` are one absolute
constant `C`, chosen before `ε, δ, n, d`; `log(e/ε) ≥ 1` replaces `log(1/ε)`. -/
theorem theorem_4_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ ε δ : ℝ, 0 < ε → ε < 1 / 2 → 0 < δ → δ < 1 / 2 →
      ∀ n d : ℕ, 1 ≤ n → 2 ≤ d →
      ∃ (N m p : ℕ) (o : Fin n × Fin d × Bool × Fin (p + 1) ↪ Fin (N * n * qd d + m))
        (gates : List (ShiShallow.Instr (N * n * qd d + m))),
        (N : ℝ) ≤ (2 : ℝ) ^ (C * ε ^ (-8 : ℝ) * Real.log (Real.exp 1 / ε) ^ C) *
            ((n : ℝ) * d) ^ 2 * Real.log (n * d / δ) ^ C ∧
        (gates.length : ℝ) ≤ (2 : ℝ) ^ (C * ε ^ (-8 : ℝ) * Real.log (Real.exp 1 / ε) ^ C) *
            (n : ℝ) ^ 3 * (d : ℝ) ^ 2 * Real.log (n * d / δ) ^ C ∧
        ∀ ρ : Matrix (Config n d) (Config n d) ℂ, WildeQIT.IsDensityOperator ρ →
          1 - δ ≤ learnSuccess ρ gates p o ε := by sorry

end TolProdTest.Supplement
