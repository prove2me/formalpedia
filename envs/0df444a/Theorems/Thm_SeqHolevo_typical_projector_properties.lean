-- Prove2me | Theorems.Thm_SeqHolevo_typical_projector_properties
-- name    : SeqHolevo.typical_projector_properties
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:00:15.724098+00:00
-- url     : https://prove2.me/theorems/3517b905-b60e-412b-9741-cda451a1d164
-- title:
--   Appendix A — the three properties of the typical projector
-- statement:
--   Let $\rho=\sum_xp_X(x)|x\rangle\langle x|$ be a density operator with a countable spectral decomposition and finite entropy $H(X)=-\sum_xp_X(x)\log_2p_X(x)$, and let $\Pi^n_{\rho,\delta}$ be its typical projector. Then:
--
--   1. for every $\varepsilon,\delta>0$ there is $N$ with $\operatorname{Tr}\{\Pi^n_{\rho,\delta}\rho^{\otimes n}\}\ge1-\varepsilon$ for all $n\ge N$;
--   2. for every $\delta>0$ and $n$, $\operatorname{Tr}\{\Pi^n_{\rho,\delta}\}\le2^{n[H(X)+\delta]}$;
--   3. for every $\delta>0$ and $n$,
--
--   $$2^{-n[H(X)+\delta]}\,\Pi^n_{\rho,\delta}\ \le\ \Pi^n_{\rho,\delta}\,\rho^{\otimes n}\,\Pi^n_{\rho,\delta}\ \le\ 2^{-n[H(X)-\delta]}\,\Pi^n_{\rho,\delta}$$
--
--   in the operator (Loewner) order.
--
--   These are the facts about typicality that the error analysis of the sequential decoder uses: the typical subspace carries almost all of the weight of $\rho^{\otimes n}$, has dimension about $2^{nH}$, and on it $\rho^{\otimes n}$ has eigenvalues about $2^{-nH}$.
--
--   Differences from the source:
--   - reading: H(X) used as a real number → hypothesis Summable (fun j => p j * logTwo (p j)); reason: the bounds are powers of 2 with exponent n[H(X) ± δ], a real number
--   - encoding: spectral decomposition ρ = Σ_x p_X(x)|x⟩⟨x| → labels in ℕ, IsSpectralDecomp ρ p u; reason: every density operator has a countable spectrum; finite spectra use zero weights
--   - reading: H̄(xⁿ) = −(1/n) log p_{Xⁿ}(xⁿ) for p_{Xⁿ}(xⁿ) = 0 → typical sequences have p_{Xⁿ}(xⁿ) > 0; reason: log 0 = −∞ gives H̄ = +∞, never within δ of H(X)
--   - encoding: log, base left to the reference → base 2 (logTwo); reason: the bounds are powers of 2
--   - generalization: blocklength n (n ≥ 1) in properties 2 and 3 → every n : ℕ, including n = 0; reason: at n = 0 both are identities between 1×1 arrays; the instances n ≥ 1 are the paper's
--   - encoding: operators on a Hilbert space; Tr, ‖·‖₁ and the order ≤ → coefficient arrays on ℓ²(J) for any index type J; Tr[XE] = realFockTracePair X E; ‖·‖₁ = traceSize; ≤ = TraceOperatorLE (finite quadratic forms); reason: published coordinate conventions (Next46.P32, Dependency50.P33, Frontier18.P01); the same operators and numbers
-- source:
--   Wilde–Guha–Tan–Lloyd, Explicit capacity-achieving receivers for optical communication and quantum reading, arXiv:1202.0518v2, Appendix A, p.6 (three displayed properties after the definition of Π^n_{ρ,δ})

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P76
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01
import Definitions.Def_SeqHolevo_idArr
import Definitions.Def_SeqHolevo_arrMul
import Definitions.Def_HolevoCQ_tensorPowMat
import Definitions.Def_SeqHolevo_IsSpectralDecomp
import Definitions.Def_SeqHolevo_typicalProjector

open QAlgorithms.Papers.Independent.Intakenext100.P76 (selfInformationMean)
open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)
open QAlgorithms.Papers.Independent.Frontier18.P01 (TraceOperatorLE)
open QAlgorithms.Papers.Independent.Next46.P32 (realFockTracePair)

namespace SeqHolevo

/-- Wilde–Guha–Tan–Lloyd, *Explicit capacity-achieving receivers for optical communication and quantum reading*, arXiv:1202.0518v2, Appendix A, p.6 (PDF page): "The three important properties of the typical projector
are as follows: `Tr{Π^n_{ρ,δ} ρ^{⊗n}} ≥ 1 − ε`, `Tr{Π^n_{ρ,δ}} ≤ 2^{n[H(X)+δ]}`,
`2^{−n[H(X)+δ]} Π^n_{ρ,δ} ≤ Π^n_{ρ,δ} ρ^{⊗n} Π^n_{ρ,δ} ≤ 2^{−n[H(X)−δ]} Π^n_{ρ,δ}`, where the first
property holds for arbitrary `ε, δ > 0` and sufficiently large `n`."

**Formalization Note.** `ρ = Σ_x p_x |u_x⟩⟨u_x|` is a countable spectral decomposition
(`IsSpectralDecomp`), `H(X) = selfInformationMean p` (bits) and `hH` says it is finite (the paper
uses `H(X)` as a real number). Traces are `realFockTracePair` (`Tr Π = Tr[Π I]`), products are
coefficientwise (`arrMul`), `≤` is the published Loewner order `TraceOperatorLE`, and `2^x` is
the real power. Clause (i) is quantified `∀ ε > 0, ∀ δ > 0, ∃ N, ∀ n ≥ N`; clauses (ii)–(iii) for
every `δ > 0` and every `n` (they hold at `n = 0` too, with Lean's `1/0 = 0` in `H̄`). -/
theorem typical_projector_properties {I : Type} (ρ : Matrix I I ℂ) (p : ℕ → ℝ)
    (u : ℕ → I → ℂ) (hdec : IsSpectralDecomp ρ p u)
    (hH : Summable (fun j => p j * logTwo (p j))) :
    (∀ ε > 0, ∀ δ > 0, ∃ N : ℕ, ∀ n ≥ N,
      1 - ε ≤ realFockTracePair (typicalProjector p u n δ) (HolevoCQ.tensorPowMat ρ n)) ∧
    (∀ δ > 0, ∀ n : ℕ,
      realFockTracePair (typicalProjector p u n δ) (idArr (Fin n → I)) ≤
        (2 : ℝ) ^ ((n : ℝ) * (selfInformationMean p + δ))) ∧
    (∀ δ > 0, ∀ n : ℕ,
      TraceOperatorLE ((↑((2 : ℝ) ^ (-((n : ℝ) * (selfInformationMean p + δ)))) : ℂ) •
          typicalProjector p u n δ)
        (arrMul (arrMul (typicalProjector p u n δ) (HolevoCQ.tensorPowMat ρ n)) (typicalProjector p u n δ)) ∧
      TraceOperatorLE
        (arrMul (arrMul (typicalProjector p u n δ) (HolevoCQ.tensorPowMat ρ n)) (typicalProjector p u n δ))
        ((↑((2 : ℝ) ^ (-((n : ℝ) * (selfInformationMean p - δ)))) : ℂ) •
          typicalProjector p u n δ)) := by sorry

end SeqHolevo
