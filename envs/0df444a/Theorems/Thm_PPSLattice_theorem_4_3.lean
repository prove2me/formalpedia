-- Prove2me | Theorems.Thm_PPSLattice_theorem_4_3
-- name    : PPSLattice.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:36:18.415278+00:00
-- url     : https://prove2.me/theorems/7d3de116-cd05-403c-9216-d8db58da7694
-- title:
--   Theorem 4.3 — one-way functions give an SEPRF with $|\mathrm{key}|=O(\lambda^2\ell_{\mathrm{out}})$
-- statement:
--   Assume one-way functions exist. Then there is an SEPRF scheme $(\mathrm{Setup},\mathrm{Eval},\mathrm{Sim1},\mathrm{Sim2})$, with polynomial-time algorithms, satisfying Definition 4.2 for every output size $\ell_{\mathrm{out}}\ge1$, and a constant $C$ such that every key output by $\mathrm{Setup}(1^\lambda,1^{\ell_{\mathrm{out}}})$, and every key output by $\mathrm{Sim2}(\mathrm{eqKey},y^*)$ for $\mathrm{eqKey}$ output by $\mathrm{Sim1}(1^\lambda,1^{\ell_{\mathrm{out}}},x^*)$, $x^*\in\{0,1\}^\lambda$, $y^*\in\{0,1\}^{\ell_{\mathrm{out}}}$, has length
--   $$|\mathrm{key}|\le C(\lambda+1)^2\ell_{\mathrm{out}}.$$
--
--   The PRF key is part of every set key $\mathrm{sk}_S$, so this size bound feeds the full-compactness analysis of §4.4.
--
--   Differences from the source:
--   - reading: one-way functions (not defined in the paper) → OWFExists: a polynomial-time f that every uniform PPT inverter inverts on f(x), x ← {0,1}^n, with negligible probability; reason: standard definition, in the machine model of every other adversary of the mission
--   - reading: for any positive polynomial ℓ_out(λ) → one scheme whose algorithms receive ℓ_out ≥ 1 in unary; reason: covers every positive polynomial ℓ_out(λ)
--   - encoding: |key| = O(λ² · ℓ_out) → |key| ≤ C(λ+1)²ℓ_out for keys output by Setup and by Sim2; reason: equivalent for λ ≥ 1, the paper's range of λ (§3, p.15, where N is the set of positive integers)
--   - reading: Eval(key, x) → y ∈ {0,1}^ℓ (syntax) → IsSEPRF requires output length ℓ_out for every key output by Setup or Sim2; reason: syntax of Eval, p.19
--   - reading: polynomial-time algorithms → SEPRF.Efficient (exact PPT samplers and a polynomial-time Eval); reason: §4.2, p.18
--   - reading: stateful (admissible) PPT adversary → uniform reactive machine RestrictedDec.Adversary (polynomial-time step function, polynomially many coins, bounded state, moves and activations); inadmissible runs scored as a uniform guess; reason: Definitions 4.1, 4.2, 4.4 say PPT adversary; the ½-convention is equivalent to admissibility because an adversary can test its own admissibility
--   - encoding: crs, keys, ciphertexts, messages, set descriptions; [N]; Z_q → bit strings Str (pairs via tup, numbers in binary, least significant bit first); [N] = Finset.Icc 1 N; Z_q = ZMod q; reason: Lean convention; same instances
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), Theorem 4.3 ([HJO+16]), p.19

import Mathlib
import Definitions.Def_PPSLattice_OWFExists
import Definitions.Def_PPSLattice_SEPRF_Efficient
import Definitions.Def_PPSLattice_SEPRF_IsSEPRF
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- **Theorem 4.3** ([HJO+16]). If one-way functions exist, there is an SEPRF scheme, for every output
size `ℓ_out ≥ 1`, whose keys have length `O(λ² · ℓ_out)`: one constant `C` bounds by `C(λ+1)²ℓ_out` every key
output by `Setup(1^λ, 1^{ℓ_out})` and every key output by `Sim2(eqKey, y*)` for `eqKey` output by
`Sim1(1^λ, 1^{ℓ_out}, x*)`, `x* ∈ {0,1}^λ`, `y* ∈ {0,1}^{ℓ_out}`.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), Theorem 4.3, p.19 ("Assuming the existence of one-way functions, there exists an SEPRF scheme for any
positive polynomial ℓ_out(λ) with |key| = O(λ² · ℓ_out)").

**Formalization Note.** `ℓ_out` is an input of the algorithms (in unary), so one scheme serves every
positive polynomial `ℓ_out(λ)`. `λ` ranges over the positive integers (§3, p.15: "We denote … the set of positive integers by N"); `O(λ²ℓ_out)` is written
`C(λ+1)²ℓ_out`, which is equivalent for `λ ≥ 1`. -/
theorem theorem_4_3 (hOWF : OWFExists) :
    ∃ F : SEPRF, F.Efficient ∧ F.IsSEPRF ∧ ∃ C : ℕ, ∀ lam lo : ℕ, 1 ≤ lam → 1 ≤ lo →
      (∀ key ∈ (F.setup lam lo).support, key.length ≤ C * (lam + 1) ^ 2 * lo) ∧
        ∀ xs : Str, xs.length = lam → ∀ ek ∈ (F.sim1 lam lo xs).support,
          ∀ ys : Str, ys.length = lo → ∀ key ∈ (F.sim2 ek ys).support,
            key.length ≤ C * (lam + 1) ^ 2 * lo := by sorry

end PPSLattice
