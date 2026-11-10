-- Prove2me | Theorems.Thm_SeededShannon_theorem_5_3
-- name    : SeededShannon.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T05:23:00.670262+00:00
-- url     : https://prove2.me/theorems/2dcaeb13-fc42-4ba0-83ae-a22cc7bc8c63
-- title:
--   Theorem 5.3 — evasive obfuscation for sparse partition agreement
-- statement:
--   Fix constants $0<p<\tau<1/2$ and $0<\gamma<p/\tau$. For every sufficiently large fixed integer $b$ there is a polynomial $N_{\min}$ such that the following holds for $n\ge N_{\min}(\lambda)$ divisible by $b$, for the family indexed by partitions $P$ of $[n]$ into $b$-element blocks with
--   $$f_P(x)=1\iff x\in\mathrm{Ball}_p(0^n)\setminus\mathrm{Bal}_P(0^n;\tau,\gamma).$$
--   Assuming injective one-way functions, there is a distributional evasive obfuscator (Definition 5.1) for this family with minimum input length $N_{\min}$; its returned seed $\sigma$ determines a partition $P_\sigma$ computable in time $\mathrm{poly}(\lambda,n)$, and $f_\sigma=f_{P_\sigma}$.
--
--   Construction 6.1 uses this obfuscator at parameters $(p,\tau,\gamma/2,b)$ to detect unbalanced channel errors.
--
--   **Formalization Note** Partitions are block labellings. As printed, $N_{\min}$ exists unconditionally and the assumption governs the obfuscator.
--
--   Differences from the source:
--   - generalization: injective one-way functions, F : {0,1}^n → {0,1}^{ℓowf} unkeyed and injective (Def. 3.2) → a keyed family injective except with negligible probability over the key (published `NoisyOWMPC.KeyedFamily.IsInjOWF`); reason: a weaker hypothesis: an unkeyed injective OWF is such a family with key length 0; this is the form given by iO + OWF [BPW16] (platform item NoisyOWMPC.theorem_3_4)
--   - encoding: every sufficiently large fixed integer b → ∃ b₀, ∀ b ≥ b₀; reason: standard meaning
--   - encoding: σ determines P_σ computable in time poly(λ, n), f_σ = f_{P_σ} → a polynomial-time map partOf from (1^λ, 1^n, σ) to the code of a b-block partition P_σ with f_σ = f_{P_σ}; reason: P_σ is the index of f_σ in the family
--   - reading: efficient / polynomial-time adversaries → nonuniform polynomial-size deterministic circuit families (`Distinguisher`, `CircFamily`); schemes are uniform machines; reason: Def. 3.1 allows non-uniform adversaries and the reductions hard-wire keys, so one nonuniform class is used throughout; a randomized adversary is matched by its best coins
--   - encoding: for every polynomially bounded n (every polynomial P) → pointwise clauses for all n ≥ N_min(λ); probabilistic clauses for every bound n ≤ (λ+2)^c; reason: the pointwise clauses hold at each length, and every polynomial is bounded by some (λ+2)^c
-- source:
--   Dujmovic, Lu, Silbak, Wichs, Shannon Rate Seeded Codes from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 52f4b606…a769709), Theorem 5.3, p.32 (PDF p.35)

import Mathlib
import Definitions.Def_NoisyOWMPC_KeyedFamily
import Definitions.Def_SeededShannon_EvObf
import Definitions.Def_SeededShannon_balP

set_option autoImplicit false

namespace SeededShannon

open LaconicBarrier NoisyOWMPC

/-- **Theorem 5.3 (Sparse Partition Agreement)** (Dujmovic, Lu, Silbak, Wichs, STOC 2027 submission
(manuscript sha256 52f4b606…a769709), Theorem 5.3, p.32): fix constants `0 < p < τ < 1/2` and
`0 < γ < p/τ`. For every sufficiently large fixed integer `b` there is a polynomial `N_min` such that,
for the family indexed by partitions `P` of `[n]` into `b`-element blocks (`n ≥ N_min(λ)` divisible by
`b`) with `f_P(x) = 1 ⟺ x ∈ Ball_p(0^n) \ Bal_P(0^n; τ, γ)`: assuming injective one-way functions,
there is a distributional evasive obfuscator for this family with minimum input length `N_min`,
whose returned seed `σ` determines a partition `P_σ` computable in time `poly(λ, n)`, with
`f_σ = f_{P_σ}`.

**Formalization Note** "Sufficiently large fixed integer `b`" is `∃ b₀, ∀ b ≥ b₀`. Partitions are
block labellings; `partOf λ n σ` is the code of `P_σ`. Injective one-way functions are the published
keyed `NoisyOWMPC.KeyedFamily.IsInjOWF`. As printed, `N_min` exists unconditionally and the
assumption governs the obfuscator. -/
theorem theorem_5_3 (p τ γ : ℝ) (hp : 0 < p) (hpτ : p < τ) (hτ : τ < 1 / 2) (hγ : 0 < γ)
    (hγτ : γ < p / τ) :
    ∃ b₀ : ℕ, ∀ b ≥ b₀, ∃ Nmin : ℕ → ℕ, PolyParam Nmin ∧
      ((∃ G : KeyedFamily, G.IsInjOWF) →
        ∃ (O : EvObf) (partOf : ℕ → ℕ → List Bool → List Bool),
          O.IsEvObf Nmin (fun _ n => b ∣ n) (partFamily53 p τ γ b) ∧
          PolyTimeOn (ι := (z : {z : ℕ × ℕ // Nmin z.1 ≤ z.2 ∧ b ∣ z.2}) ×
              (Fin (O.progCoins z.1.1 z.1.2) → Bool))
            (fun i => [unary i.1.1.1, unary i.1.1.2, (O.genProg i.1.1.1 i.1.1.2 i.2).1])
            (fun i => partOf i.1.1.1 i.1.1.2 (O.genProg i.1.1.1 i.1.1.2 i.2).1) ∧
          ∀ lam n, Nmin lam ≤ n → b ∣ n → ∀ r : Fin (O.progCoins lam n) → Bool,
            ∃ P : Fin n → ℕ, IsBlockPartition b n P ∧
              partOf lam n (O.genProg lam n r).1 = partCode P ∧
              ∀ x : Fin n → Bool, O.func lam n (O.genProg lam n r).1 x = true ↔
                (ballP p (fun _ => false) x ∧ ¬ balP b τ γ P (fun _ => false) x)) := by sorry

end SeededShannon
