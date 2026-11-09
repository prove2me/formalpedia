-- Prove2me | Theorems.Thm_TreeEquivalenceHORS_Equivalence_theorem_5_8
-- name    : TreeEquivalenceHORS.Equivalence.theorem_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:44:10.32197+00:00
-- url     : https://prove2.me/theorems/977fa8be-9740-421a-988c-303020826d48
-- title:
--   Theorem 5.8 (Intermediate compilation): $M\mapsto(G^L_M,G^R_M)$ is effective, safe, productive, of order $\le4$, and $M\!\downarrow$ iff the schemes disagree at some address
-- statement:
--   The construction $M\mapsto(G^L_M,G^R_M)$ is effective and produces well-formed, safe, productive schemes of order at most four over $\Sigma_0$. Moreover, writing $S$ for the start symbol of each scheme,
--   $$M\!\downarrow\iff\exists w\in\mathbb N^*\ \exists a,b\in\Sigma_0\ \bigl[a\ne b\wedge\mathrm{Obs}_{G^L_M}(S,w,a)\wedge\mathrm{Obs}_{G^R_M}(S,w,b)\bigr].$$
--
--   This is the lower-bound reduction before the final change of alphabet.
--
--   Differences from the source:
--   - encoding: the construction is effective / total computable → `Computable` (Mathlib) of the induced map on natural-number codes: decode, apply the construction, encode (malformed codes go to the code of `none`); reason: the standard meaning of effectiveness of a syntax transformation under fixed encodings
--   - encoding: standard computable injective encodings of finite syntax by natural numbers, with total computable decoders that return syntax or reject → the derived `Encodable` instances of `Ty`, `Tm`, `HORS`, `Instr` (and their products, lists, options); a code on which `Encodable.decode` returns `none` is malformed; reason: the derived encoding is injective with a total, structurally recursive decoder; computability classes of predicates on ℕ do not depend on which such encoding is fixed
--   - encoding: Σ₀ = {z:0, a:1, b:3}, Σ₂ = {e:0, d:2} → `sigma0 = [0, 1, 3]` (terminals 0 = z, 1 = a, 2 = b) and `sigma2 = [0, 2]` (0 = e, 1 = d); reason: a ranked alphabet is its list of arities, terminals named by position
-- source:
--   Mingkun Xiao, Yixuan Sun, Tree Equivalence of Higher-Order Recursion Schemes Is Undecidable, STOC 2027 submission #421 (October 2026), source.pdf SHA-256 e875d09ced029e3f5cb114abba049e4a2b1bdaa9b064c98b0d71f2ec7451c7af, Theorem 5.8, printed p. 20 / PDF p. 22

import Mathlib
import Definitions.Def_TreeEquivalenceHORS_Equivalence_Compiler

namespace TreeEquivalenceHORS.Equivalence

/-- **Theorem 5.8 (Intermediate compilation)** (printed p. 20 / PDF p. 22). The construction
`M ↦ (G^L_M, G^R_M)` is effective (its action on codes is total computable) and produces
well-formed safe productive schemes of order at most four over `Σ₀`; moreover
`M↓ ⟺ ∃ w ∈ ℕ* ∃ a, b ∈ Σ₀, a ≠ b ∧ Obs_{G^L_M}(S, w, a) ∧ Obs_{G^R_M}(S, w, b)`. -/
theorem theorem_5_8 :
    Computable (fun n : ℕ => Encodable.encode
      ((Encodable.decode n : Option Machine).map fun M => (compile .L M, compile .R M))) ∧
    (∀ (M : Machine) (side : Side),
      (compile side M).Valid ∧ (compile side M).Safe ∧ (compile side M).Prod ∧
        (compile side M).alphabet = sigma0 ∧ (compile side M).order ≤ 4) ∧
    ∀ M : Machine, M.Halts ↔
      ∃ (w : List ℕ) (a b : ℕ), a < sigma0.length ∧ b < sigma0.length ∧ a ≠ b ∧
        (compile .L M).Obs (.nt (compile .L M).start) w a ∧
        (compile .R M).Obs (.nt (compile .R M).start) w b := by sorry

end TreeEquivalenceHORS.Equivalence
