-- Prove2me | Theorems.Thm_UnitaryQIPPSPACE_corollary_4_8
-- name    : UnitaryQIPPSPACE.corollary_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:35:28.699201+00:00
-- url     : https://prove2.me/theorems/7b2d695d-c457-4992-abe6-3cca8b6495d0
-- title:
--   Corollary 4.8 — approximation by a PSPACE-oracle circuit
-- statement:
--   Let $\{U_n\}\in\mathsf{unitaryPSPACE}_\gamma$ with $0\le\gamma(n)\le2^{-10}$. There are $n_0$, a language $A\in\mathsf{PSPACE}$ and a polynomial-time generator of unitary oracle circuits $C_{n,\beta}$ (on $(1^n,1^\beta)$, $n,\beta\ge1$, size $\mathrm{poly}(n+\beta)$) such that for every $\beta:\mathbb N\to\mathbb N$ with $1^{\beta(n)}$ polynomial-time computable from $1^n$: $C_{n,\beta(n)}$ is generated from $1^n$ in polynomial time, and for every $n\ge n_0$, with $\Phi_n(\rho)=\operatorname{tr}_E[C^A_{n,\beta(n)}\iota\rho\iota^\dagger(C^A_{n,\beta(n)})^\dagger]$,
--   $$D_\diamond(\Phi_n,\mathcal U_n)\le16\sqrt{\gamma(n)}+2^{-\beta(n)-1}.$$
--
--   Differences from the source:
--   - reading: "Take W and n₀ as in Proposition 4.5, and A_W, C_{n,β}, E, ι as in Lemma 4.7" → ∃ n₀, A ∈ PSPACE and a polynomial-time generator (with size bound), chosen before β(·); reason: the self-contained form of the cross-references; these objects do not depend on β(·)
--   - encoding: the gate set G is fixed "without loss of generality, … for example, {H, T, CNOT}" → G = {H, T, CNOT} exactly; reason: the paper's own example; the classes do not depend on the choice of a finite universal gate set
--   - encoding: deterministic Turing machines → the published oracle Turing machines QAdvFew.PoQOracle.OTM run with the empty oracle; descriptions are tuple codes; reason: a standard machine model and a fixed injective code; polynomial time and space are preserved
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), Corollary 4.8, p.25 (PDF p.27)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity
import Definitions.Def_QAdvFew_PoQOracle_OTM
import Definitions.Def_QAdvFew_PoQOracle_PSPACE
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_UnitaryQIPPSPACE_unitaryPSPACEd
import Definitions.Def_UnitaryQIPPSPACE_OCirc
import Definitions.Def_UnitaryQIPPSPACE_diamondDist
import Definitions.Def_UnitaryQIPPSPACE_conjBy

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace UnitaryQIPPSPACE

/-- **Corollary 4.8** (He, Ou, Zhao, *unitaryQIP = unitaryPSPACE*, arXiv:2611.02819, held version
sha256 9e357a00…, pp. 25–26 (PDF pp. 27–28)): "Let `{U_n} ∈ unitaryPSPACE_γ` with `γ(n) ≤ 2^{−10}`
for all `n`. Take `W = {W_n}` and `n₀` as in Proposition 4.5, and `A_W, C^{(·)}_{n,β}, E, ι` as in
Lemma 4.7. Let `β : ℕ → ℕ` be such that `1^{β(n)}` is polynomial-time computable from `1^n`. Define
`Φ_n(ρ) := tr_E[C^{A_W}_{n,β(n)} · ιρι† · (C^{A_W}_{n,β(n)})†]`. Then `C^{(·)}_{n,β(n)}` can be generated
from `1^n` in polynomial time, and for every `n ≥ n₀`, `D⋄(Φ_n, 𝒰_n) ≤ 16√γ(n) + 2^{−β(n)−1}`. (17)"

Self-contained form: there are `n₀`, a language `A ∈ PSPACE` and a polynomial-time generator of
unitary oracle circuits `C_{n,β}` on `(1^n, 1^β)`, `n, β ≥ 1`, of size `poly(n + β)` (the objects of
Proposition 4.5 and Lemma 4.7, which do not depend on `β(·)`), such that for every `β(·)` with
`1^{β(n)}` computable from `1^n` in polynomial time, `C_{n,β(n)}` is generated from `1^n` in polynomial
time and `D⋄(Φ_n, 𝒰_n) ≤ 16√γ(n) + 2^{−β(n)−1}` for every `n ≥ n₀`, with `𝒰_n(ρ) = U_n ρ U_n†`.

**Formalization Note** Machines are the published `QAdvFew.PoQOracle.OTM` with the empty oracle;
`PSPACE` is `QAdvFew.PoQOracle.PSPACE` with the empty oracle. -/
theorem corollary_4_8 (U : UFam) (γ : ℕ → ℝ) (hγ : ∀ n, 0 ≤ γ n ∧ γ n ≤ (1 / 2 : ℝ) ^ 10)
    (hU : U ∈ unitaryPSPACEd γ) :
    ∃ (n₀ : ℕ) (A : Set Str), A ∈ PSPACE noOracle ∧
      ∃ (Cg : ℕ → ℕ → OCirc) (M : OTM) (p P : Polynomial ℕ),
        (∀ n β : ℕ, 1 ≤ n → 1 ≤ β →
          M.result noOracle (tup [unary n, unary β]) (p.eval (n + β)) ≠ none ∧
          M.output noOracle (tup [unary n, unary β]) (p.eval (n + β)) = (Cg n β).code ∧
          (Cg n β).size ≤ P.eval (n + β) ∧ (Cg n β).Valid n) ∧
        ∀ β : ℕ → ℕ, (∃ (Mβ : OTM) (pβ : Polynomial ℕ), ∀ n,
            Mβ.result noOracle (unary n) (pβ.eval n) ≠ none ∧
            Mβ.output noOracle (unary n) (pβ.eval n) = unary (β n)) →
          (∃ (M' : OTM) (p' : Polynomial ℕ), ∀ n,
            M'.result noOracle (unary n) (p'.eval n) ≠ none ∧
            M'.output noOracle (unary n) (p'.eval n) = (Cg n (β n)).code) ∧
          ∀ n ≥ n₀, diamondDist (oracleChannel (langOracle A) (Cg n (β n)) n)
              (conjBy (U n : Matrix (Bits n) (Bits n) ℂ))
            ≤ 16 * Real.sqrt (γ n) + (1 / 2 : ℝ) ^ (β n + 1) := by sorry

end UnitaryQIPPSPACE
