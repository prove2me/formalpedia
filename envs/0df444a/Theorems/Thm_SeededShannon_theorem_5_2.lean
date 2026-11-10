-- Prove2me | Theorems.Thm_SeededShannon_theorem_5_2
-- name    : SeededShannon.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:46:14.577431+00:00
-- url     : https://prove2.me/theorems/b0062f0d-eb40-4670-bab4-0c369956a30a
-- title:
--   Theorem 5.2 — evasive obfuscation for sparse set agreement
-- statement:
--   For every constant $0<p<1$ there are a polynomial $N_{\min}$, a constant $\gamma>0$ and an efficiently computable integer bound $B(\lambda,n)=O(n^{1-\gamma})$ such that the following holds for the family
--   $$\mathcal F_{\lambda,n}=\{f_S:S\subseteq[n],\ |S|\le B(\lambda,n)\},\qquad f_S(x)=1\iff\delta(x)\le p\wedge x_S=1.$$
--   Assuming injective one-way functions, there is a distributional evasive obfuscator (Definition 5.1) for $\mathcal F_{\lambda,n}$ with minimum input length $N_{\min}$; its seed $\sigma$ determines a set $S_\sigma$ computable in time $\mathrm{poly}(\lambda,n)$, and $f_\sigma=f_{S_\sigma}$.
--
--   Construction 6.1 uses this obfuscator at density $p/\tau$ to test whether every header chunk of the hidden set is heavily corrupted.
--
--   **Formalization Note** Sets are indicator vectors. As printed, $N_{\min},\gamma,B$ exist unconditionally and the assumption governs the obfuscator.
--
--   Differences from the source:
--   - generalization: injective one-way functions, F : {0,1}^n → {0,1}^{ℓowf} unkeyed and injective (Def. 3.2) → a keyed family injective except with negligible probability over the key (published `NoisyOWMPC.KeyedFamily.IsInjOWF`); reason: a weaker hypothesis: an unkeyed injective OWF is such a family with key length 0; this is the form given by iO + OWF [BPW16] (platform item NoisyOWMPC.theorem_3_4)
--   - encoding: B = O(n^{1−γ}) → B(λ, n) ≤ C · n^{1−γ} for one constant C, all λ and all n ≥ N_min(λ); reason: the family is defined for n ≥ N_min(λ)
--   - encoding: σ determines S_σ computable in time poly(λ, n), f_σ = f_{S_σ} → a polynomial-time map setOf from (1^λ, 1^n, σ) to the indicator of S_σ, with |S_σ| ≤ B and f_σ = f_{S_σ}; reason: S_σ is the index of f_σ in the family
--   - reading: efficient / polynomial-time adversaries → nonuniform polynomial-size deterministic circuit families (`Distinguisher`, `CircFamily`); schemes are uniform machines; reason: Def. 3.1 allows non-uniform adversaries and the reductions hard-wire keys, so one nonuniform class is used throughout; a randomized adversary is matched by its best coins
--   - encoding: for every polynomially bounded n (every polynomial P) → pointwise clauses for all n ≥ N_min(λ); probabilistic clauses for every bound n ≤ (λ+2)^c; reason: the pointwise clauses hold at each length, and every polynomial is bounded by some (λ+2)^c
-- source:
--   Dujmovic, Lu, Silbak, Wichs, Shannon Rate Seeded Codes from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 52f4b606…a769709), Theorem 5.2, p.31 (PDF p.34)

import Mathlib
import Definitions.Def_NoisyOWMPC_KeyedFamily
import Definitions.Def_SeededShannon_EvObf
import Definitions.Def_SeededShannon_setFamily

set_option autoImplicit false

namespace SeededShannon

open LaconicBarrier NoisyOWMPC

/-- **Theorem 5.2 (Sparse Set Agreement)** (Dujmovic, Lu, Silbak, Wichs, STOC 2027 submission
(manuscript sha256 52f4b606…a769709), Theorem 5.2, p.31): for every constant `0 < p < 1` there are a
polynomial `N_min`, a constant `γ > 0` and an efficiently computable integer-valued bound
`B(λ, n) = O(n^{1−γ})` such that, for the family `F_{λ,n} = {f_S : S ⊆ [n], |S| ≤ B(λ, n)}` with
`f_S(x) = 1 ⟺ δ(x) ≤ p ∧ x_S = 1`: assuming injective one-way functions, there is a distributional
evasive obfuscator for `F_{λ,n}` with minimum input length `N_min`, whose seed `σ` determines a set
`S_σ` computable in time `poly(λ, n)` with `f_σ = f_{S_σ}`.

**Formalization Note** Sets are indicator vectors; `setOf λ n σ` is the indicator vector of `S_σ`.
`B = O(n^{1−γ})` is `B(λ, n) ≤ C · n^{1−γ}` for one `C`, all `λ` and all `n ≥ N_min(λ)`. Injective
one-way functions are the published keyed `NoisyOWMPC.KeyedFamily.IsInjOWF`. As printed,
`N_min`, `γ`, `B` exist unconditionally and the assumption governs the obfuscator. -/
theorem theorem_5_2 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ (Nmin : ℕ → ℕ) (γ : ℝ) (B : ℕ → ℕ → ℕ), PolyParam Nmin ∧ 0 < γ ∧ EffComputable₂ B ∧
      (∃ C : ℝ, ∀ lam n, Nmin lam ≤ n → (B lam n : ℝ) ≤ C * (n : ℝ) ^ (1 - γ)) ∧
      ((∃ G : KeyedFamily, G.IsInjOWF) →
        ∃ (O : EvObf) (setOf : ℕ → ℕ → List Bool → List Bool),
          O.IsEvObf Nmin (fun _ _ => True) (setFamily p B) ∧
          PolyTimeOn (ι := (z : {z : ℕ × ℕ // Nmin z.1 ≤ z.2}) ×
              (Fin (O.progCoins z.1.1 z.1.2) → Bool))
            (fun i => [unary i.1.1.1, unary i.1.1.2, (O.genProg i.1.1.1 i.1.1.2 i.2).1])
            (fun i => setOf i.1.1.1 i.1.1.2 (O.genProg i.1.1.1 i.1.1.2 i.2).1) ∧
          ∀ lam n, Nmin lam ≤ n → ∀ r : Fin (O.progCoins lam n) → Bool,
            ∃ S : Fin n → Bool, setOf lam n (O.genProg lam n r).1 = bits S ∧ wt S ≤ B lam n ∧
              ∀ x : Fin n → Bool, O.func lam n (O.genProg lam n r).1 x = true ↔ setAgree p S x) := by sorry

end SeededShannon
