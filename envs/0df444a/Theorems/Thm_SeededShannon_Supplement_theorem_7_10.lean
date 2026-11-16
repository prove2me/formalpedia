-- Prove2me | Theorems.Thm_SeededShannon_Supplement_theorem_7_10
-- name    : SeededShannon.Supplement.theorem_7_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:45:46.537383+00:00
-- url     : https://prove2.me/theorems/44a4970a-5faf-486e-9a33-5b94bd816eec
-- title:
--   Theorem 7.10 — list decoding and pruning gives unique decoding
-- statement:
--   Let $\Pi_H$ be a subexponentially secure hash family as in Definition 7.6, with constant $c$ and sparsity threshold $s_0$. Let $p,\eta\ge0$ be constants with $2p+2\eta<1/2$, put
--   $$r=p+\eta+\tfrac14,\qquad g(\lambda)=2\ell_{\mathrm{lab}}(\lambda)+2\lambda,$$
--   and let $a_r,c_r$ be the constants of Lemma 7.9. Choose polynomials $\kappa=\kappa(\lambda)$ and $v=v(\lambda)$ with
--   $$\kappa^c\ge g(\lambda)+1,\qquad a_r\sqrt v\ge s_0(\kappa),\qquad c_r\sqrt v\ge (g(\lambda)+1)\ln 2,$$
--   and let $H_K=\mathrm{Hash}(K,\cdot)$ with $K\leftarrow\mathrm{Gen}(1^\kappa,1^k,1^v)$. Let $\Pi_{\mathrm{base}}$ be a seeded code for messages of length $k+v$ that is selectively $(p,L)$-correct with a $p$-sound decoder, and that has $(\eta,\ell_{\mathrm{lab}})$-permuted-linear structure over a $Q$-pairwise column robust encoder $E$, for a polynomial $Q$. Then Construction 7.1 is a uniquely decodable seeded code that selectively $p$-corrects with unique decoding, with the codeword length and supported lengths of $\Pi_{\mathrm{base}}$. Its algorithms run the base algorithms once, plus time $\mathrm{poly}(\lambda,k)$.
--
--   This is the generic transformation from list decoding to unique decoding for radius $p<1/4$.
--
--   **Formalization Note** The constants $a_r,c_r>0$ of the cited Lemma 7.9 are existential and depend only on $r$.
--
--   Differences from the source:
--   - encoding: let a_r, c_r be the constants of Lemma 7.9 (depending only on r) → ∀ r, ∃ a_r c_r > 0 chosen before Π_H and all other data; reason: Lemma 7.9 is cited without proof and only names its constants
--   - reading: Π_base a seeded code (Definition 3.15, three efficient algorithms); its algorithms run the base algorithms once, plus time poly(λ, k) → hypothesis SeededCode.IsEfficient for Π_base; conclusion SeededCode.IsEfficient for Construction 7.1 at its supported lengths; reason: the asymptotic content of the running-time claim
--   - encoding: uniquely decodable; selectively p-corrects with unique decoding → list bound 1 and failure Decode(y) ≠ [x*]; reason: Definition 3.15 identifies a unique output with a list of size at most one
--   - encoding: the codeword length and supported lengths of Π_base → N_u(λ, k) = N(λ, k + v(λ)), k supported iff k + v(λ) is; reason: definitional in Construction 7.1
-- source:
--   Dujmovic, Lu, Silbak, Wichs, Shannon Rate Seeded Codes from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 52f4b606…a769709), Theorem 7.10, p.51 (PDF p.54); Construction 7.1, p.48; Definitions 7.2, 7.4, 7.6, pp.49–50

import Mathlib
import Definitions.Def_SeededShannon_Supplement_SelectivelyCorrectUnique
import Definitions.Def_SeededShannon_Supplement_CIHash
import Definitions.Def_SeededShannon_Supplement_HasPermLinear
import Definitions.Def_SeededShannon_Supplement_constr71

set_option autoImplicit false

namespace SeededShannon.Supplement

open NoisyOWMPC SeededShannon

/-- **Theorem 7.10 (List decoding and pruning)** (Dujmovic, Lu, Silbak, Wichs, *Shannon Rate Seeded
Codes from Indistinguishability Obfuscation*, STOC 2027 submission (manuscript sha256
52f4b606…a769709), Theorem 7.10, p.51): let `Π_H` be a subexponentially secure hash family as in
Definition 7.6, with constant `c` and sparsity threshold `s₀`. Let `p, η ≥ 0` with `2p + 2η < 1/2`,
`r = p + η + 1/4`, `g(λ) = 2ℓ_lab(λ) + 2λ`, and let `a_r, c_r` be the constants of Lemma 7.9. Choose
polynomials `κ`, `v` with `κ^c ≥ g + 1`, `a_r √v ≥ s₀(κ)`, `c_r √v ≥ (g + 1) ln 2` (7.5). Let `Π_base`
be a seeded code for messages of length `k + v` that is selectively `(p, L)`-correct with a `p`-sound
decoder and has `(η, ℓ_lab)`-permuted-linear structure over a `Q`-pairwise column robust encoder `E`,
for a polynomial `Q`. Then Construction 7.1 is a uniquely decodable seeded code that selectively
`p`-corrects with unique decoding, with the codeword length and supported lengths of `Π_base`. Its
algorithms run the base algorithms once, plus time `poly(λ, k)`.

**Formalization Note** The constants of the cited Lemma 7.9 are existential: for each `r` there are
`a_r, c_r > 0`, chosen before `Π_H` and everything else (Lemma 7.9: "depending only on `r`"), for
which the theorem holds. Lemma 7.9 itself is not a hypothesis. Seeded codes, list size, soundness
and selective correctness are the published `SeededShannon.SeededCode` notions; the base code
supports the lengths `supp`, and the transformed code supports `k` when the base supports `k + v(λ)`.
Unique decodability is list size `1`. `Π_base` is a seeded code in the sense of Definition 3.15 (p.22: "three efficient algorithms"), so its
efficiency (`SeededCode.IsEfficient`) is a hypothesis; "runs the base algorithms once plus
`poly(λ, k)`" is stated as the efficiency of Construction 7.1 at its supported lengths. -/
theorem theorem_7_10 : ∀ r : ℝ, ∃ ar cr : ℝ, 0 < ar ∧ 0 < cr ∧
    ∀ (H : CIHash) (c : ℝ) (s₀ : ℕ → ℕ), H.IsEfficient → H.SubexpCI c s₀ →
    ∀ p η : ℝ, 0 ≤ p → 0 ≤ η → 2 * p + 2 * η < 1 / 2 → r = p + η + 1 / 4 →
    ∀ lablen κ v : ℕ → ℕ, PolyBounded κ → PolyBounded v →
      (∀ lam, ((2 * lablen lam + 2 * lam + 1 : ℕ) : ℝ) ≤ (κ lam : ℝ) ^ c) →
      (∀ lam, (s₀ (κ lam) : ℝ) ≤ ar * Real.sqrt (v lam)) →
      (∀ lam, ((2 * lablen lam + 2 * lam + 1 : ℕ) : ℝ) * Real.log 2 ≤ cr * Real.sqrt (v lam)) →
    ∀ (C : SeededCode) (supp : ℕ → ℕ → Prop) (L Q : ℕ → ℕ → ℕ), PolyBounded₂ Q →
      C.IsEfficient supp →
      C.EncodeLength supp → C.ListBound supp L → C.Sound supp p → C.SelectivelyCorrect supp p →
      (∃ E lab π s, HasPermLinear C supp v η lablen E lab π s ∧
        ∀ lam k, supp lam (k + v lam) → ColRobust (E lam k) (Q k (v lam))) →
      (constr71 C H κ v).EncodeLength (fun lam k => supp lam (k + v lam)) ∧
      (constr71 C H κ v).ListBound (fun lam k => supp lam (k + v lam)) (fun _ _ => 1) ∧
      SelectivelyCorrectUnique (constr71 C H κ v) (fun lam k => supp lam (k + v lam)) p ∧
      (constr71 C H κ v).IsEfficient (fun lam k => supp lam (k + v lam)) := by sorry

end SeededShannon.Supplement
