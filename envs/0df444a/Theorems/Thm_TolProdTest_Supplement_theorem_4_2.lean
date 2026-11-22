-- Prove2me | Theorems.Thm_TolProdTest_Supplement_theorem_4_2
-- name    : TolProdTest.Supplement.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:09:51.362822+00:00
-- url     : https://prove2.me/theorems/9f750270-628f-432b-8116-1137c76a3636
-- title:
--   Theorem 4.2 — qudit high-fidelity product-state learner, $\tilde O(nd/\varepsilon_{\mathrm{hfl}})$ copies and $\tilde O((nd)^2/\varepsilon_{\mathrm{hfl}})$ gates
-- statement:
--   Let $n\ge1$, $d\ge2$, $\varepsilon_{\mathrm{hfl}}\in(0,1/6]$ and $\delta\in(0,1/2)$. There is a quantum algorithm which, given independent copies of an unknown mixed state $\rho\in\mathcal D((\mathbb C^d)^{\otimes n})$ satisfying
--
--   $$
--   F_{\mathrm{prod}}(\rho)\ \ge\ \tfrac56+\varepsilon_{\mathrm{hfl}},
--   $$
--
--   outputs with probability at least $1-\delta$ a classical description of a pure product state $|\hat u\rangle$ such that
--
--   $$
--   \langle\hat u|\rho|\hat u\rangle\ \ge\ F_{\mathrm{prod}}(\rho)-\varepsilon_{\mathrm{hfl}},
--   $$
--
--   with sample complexity $\tilde O(nd/\varepsilon_{\mathrm{hfl}})$ and computational complexity $\tilde O((nd)^2/\varepsilon_{\mathrm{hfl}})$, where $\tilde O$ suppresses polylogarithmic factors in $nd/(\varepsilon_{\mathrm{hfl}}\delta)$.
--
--   Precisely: there is an absolute constant $C>0$ such that for all such parameters there is a circuit over $\{H,S,T,X,\mathrm{CNOT}\}$, fixed before $\rho$, on $N$ encoded copies of $\rho$ and ancillas, with
--
--   $$
--   N\le C\,\frac{nd}{\varepsilon_{\mathrm{hfl}}}\log\!\Big(\frac{nd}{\varepsilon_{\mathrm{hfl}}\delta}\Big)^{C},\qquad \#\text{gates}\le C\,\frac{(nd)^2}{\varepsilon_{\mathrm{hfl}}}\log\!\Big(\frac{nd}{\varepsilon_{\mathrm{hfl}}\delta}\Big)^{C},
--   $$
--
--   which succeeds with probability at least $1-\delta$ on every density operator satisfying the promise. Nothing is claimed outside the promise.
--
--   This is the qudit version of the high-fidelity learner of Bakshi et al. (Theorem 4.20 of [BBK+24]); the agnostic learner of Theorem 4.1 applies it blockwise. The paper proves it in Appendix A.
--
--   **Formalization Note** Same algorithm model and fixed output decoder as Theorem 4.1. The upper end $\varepsilon_{\mathrm{hfl}}=1/6$ is included, as printed.
--
--   Differences from the source:
--   - encoding: a quantum algorithm (no model named) → a gate list over ShiShallow.Instr {H,S,T,X,CNOT} on ρ^{⊗N} encoded qudit by qudit (Nat.clog 2 d wires per qudit, little-endian, copy-major) plus m ancillas in |0⟩, intermediate measurements and classical post-processing deferred into the circuit, fixed before ρ; sample complexity = N, computational complexity = number of gates; reason: the published goal's model (TolProdTest.theorem_1_1, paper.md decision 3); a fixed finite universal gate set matches any other up to the polylogarithmic factors already allowed (Solovay–Kitaev)
--   - encoding: outputs a classical description of a pure product state |û⟩ → every wire is measured and |û⟩ = prodVec (decodeProd p o y): sign plus p-bit fixed point for the real and imaginary part of each amplitude on wires chosen by an injective map o, then per-site normalization (zero ↦ |0⟩); the algorithm chooses p and o only; reason: a classical description is a bit string; finite-precision amplitudes reach every direction up to arbitrarily small error, and the decoder is fixed so no unbounded computation is hidden outside the gate count
--   - encoding: Õ(nd/ε_hfl) copies and Õ((nd)^2/ε_hfl) computational complexity, Õ suppressing polylogarithmic factors in nd/(ε_hfl δ) → one absolute C > 0 chosen before ε_hfl, δ, n, d with N ≤ C (nd/ε_hfl) log(nd/(ε_hfl δ))^C and gates ≤ C ((nd)^2/ε_hfl) log(nd/(ε_hfl δ))^C; reason: the paper's own definition of Õ here; log(nd/(ε_hfl δ)) ≥ log 24 > 1
-- source:
--   Bao, Helsen, Nguyen, Fully tolerant product state testing and closest product state learning, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), Theorem 4.2, eqs. (83)–(84), p.20 (proof Appendix A, pp.43–44)

import Mathlib
import Definitions.Def_TolProdTest_fprod
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_TolProdTest_Supplement_learnSuccess

set_option autoImplicit false

open Matrix

namespace TolProdTest.Supplement

/-- **Theorem 4.2 (High-fidelity product state learner, qudit version of Theorem 4.20 of [BBK+24])**, Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), p.20
(proof in Appendix A, pp.43–44): "Given n ≥ 1, d ≥ 2, ε_hfl ∈ (0, 1/6], δ ∈ (0, 1/2), and independent copies of an
unknown mixed state ρ ∈ D((C^d)^{⊗n}), satisfying F_prod(ρ) ≥ 5/6 + ε_hfl, (83) there is a quantum algorithm which,
with probability at least 1 − δ, outputs a classical description of a pure product state |û⟩, such that
⟨û|ρ|û⟩ ≥ F_prod(ρ) − ε_hfl, (84) with sample complexity Õ(nd/ε_hfl) and computational complexity
Õ((nd)^2/ε_hfl). In these bounds, Õ suppresses polylogarithmic factors in nd/(ε_hfl δ), including the dependence on
the failure probability δ."

There is an absolute constant `C > 0` such that for all `ε_hfl ∈ (0, 1/6]`, `δ ∈ (0, 1/2)`, `n ≥ 1`, `d ≥ 2` there
is a circuit over `{H, S, T, X, CNOT}` on `N` encoded copies of `ρ` and `m` ancillas, with a precision `p` and an
output wire map `o`, all fixed before `ρ`, with `N ≤ C (nd/ε_hfl) log(nd/(ε_hfl δ))^C` and at most
`C ((nd)^2/ε_hfl) log(nd/(ε_hfl δ))^C` gates, such that for every density operator `ρ` with
`F_prod(ρ) ≥ 5/6 + ε_hfl` the decoded pure product state `|û⟩` satisfies `⟨û|ρ|û⟩ ≥ F_prod(ρ) − ε_hfl` with
probability at least `1 − δ`.

**Formalization Note** Same algorithm model and output decoder as `theorem_4_1` (the published goal's circuit model
plus the fixed decoder `decodeProd`). `Õ` is read as the paper defines it here: a factor `log(nd/(ε_hfl δ))^C`
with one absolute constant `C` (also the multiplicative constant), chosen before `ε_hfl, δ, n, d`;
`log(nd/(ε_hfl δ)) ≥ log 24 > 1`. No guarantee is claimed for `ρ` outside the promise (83). -/
theorem theorem_4_2 :
    ∃ C : ℝ, 0 < C ∧ ∀ ε δ : ℝ, 0 < ε → ε ≤ 1 / 6 → 0 < δ → δ < 1 / 2 →
      ∀ n d : ℕ, 1 ≤ n → 2 ≤ d →
      ∃ (N m p : ℕ) (o : Fin n × Fin d × Bool × Fin (p + 1) ↪ Fin (N * n * qd d + m))
        (gates : List (ShiShallow.Instr (N * n * qd d + m))),
        (N : ℝ) ≤ C * ((n : ℝ) * d / ε) * Real.log (n * d / (ε * δ)) ^ C ∧
        (gates.length : ℝ) ≤ C * (((n : ℝ) * d) ^ 2 / ε) * Real.log (n * d / (ε * δ)) ^ C ∧
        ∀ ρ : Matrix (Config n d) (Config n d) ℂ, WildeQIT.IsDensityOperator ρ →
          5 / 6 + ε ≤ fprod ρ → 1 - δ ≤ learnSuccess ρ gates p o ε := by sorry

end TolProdTest.Supplement
