-- Prove2me | Theorems.Thm_SubspaceEvasion312_Explicit_Supplement_evasive_subcode
-- name    : SubspaceEvasion312.Explicit.Supplement.evasive_subcode
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:48:43.925944+00:00
-- url     : https://prove2.me/theorems/a50ff310-e36c-4d05-ab7d-b3e957f7b094
-- title:
--   Theorem 28 — subcodes cut out by evasive sets are list-recoverable
-- statement:
--   There is an absolute constant $K$ with the following property. Let $\mathbb F_q$ be a finite field, let $s,n,k,r,c,\ell\ge1$ be integers and $R,\varepsilon,\rho>0$ reals. Let $A\subseteq\mathbb F_q^k$ be an $(r,c)$ subspace evasive set with $|A|\ge q^{(1-\varepsilon/2)k}$. Let $\mathrm{Enc}:\mathbb F_q^k\to(\mathbb F_q^s)^n$ be an encoder of an additive code $C$ (linear, image $C$, $k=\dim C$) with
--   $$\frac{k}{sn}\ge R+\varepsilon,$$
--   and let $C$ be $(\rho,\ell,r)$ dimension list-recoverable. Then:
--
--   1. $\mathrm{Enc}(A)\subseteq(\mathbb F_q^s)^n$ is $(\rho,\ell,c)$ list-recoverable;
--   2. $\mathrm{rate}(\mathrm{Enc}(A))=\log_q|\mathrm{Enc}(A)|/(sn)\ge R$;
--   3. if $A$ is constructable in time $T_A$ (word bound $B_A$) by a program $P_A$ and $\mathrm{Enc}$ is computed in time $T_{\mathrm{Enc}}$ (word bound $B_{\mathrm{Enc}}$) by a program $P_{\mathrm{Enc}}$, then $\mathrm{Enc}(A)$ is encodable in time $K(T_A+T_{\mathrm{Enc}})$ with a word bound at most $(B_A+B_{\mathrm{Enc}}+T_A+T_{\mathrm{Enc}}+2)^K$, for the same ordering of the field.
--
--   This is the Guruswami–Wang subcode paradigm: any dimension list-recoverable additive code becomes a nonlinear code with constant output list size once its messages are restricted to an evasive set.
--
--   **Formalization Note** Time is measured in the mission's published register machine (field operations one step, program size charged).
--
--   Differences from the source:
--   - generalization: A constructable in time T_A is a hypothesis of the whole theorem → constructability is assumed only in the encoding-time clause; reason: the list-recovery and rate clauses hold without it; with the hypothesis added the statement is the source's
--   - generalization: ρ ∈ [0, 1] in Definition 27 and ρ > 0 in the theorem → every real ρ > 0; reason: the definition is total for ρ > 1 and the same conclusion holds; it specializes to ρ ∈ (0, 1]
--   - reading: encoding time T_A + T_Enc → charged time K·(T_A + T_Enc) with absolute K and word bound (B_A + B_Enc + T_A + T_Enc + 2)^K; reason: footnote 4 fixes operation costs only up to O(1); composing two programs in a fixed instruction set costs a constant factor for moving the k message symbols and relocating jumps
--   - encoding: Enc : F_q^k → (F_q^s)^n the encoding map of a code C of rate k/(sn) → IsEncoder C E: E linear, range E = C, k = dim C; reason: the encoder definition of printed p. 7; the rate k/(sn) presupposes k = dim C
--   - encoding: lies in an r-dimensional subspace → lies in a subspace of dimension at most r; reason: a subspace of dimension at most r lies in one of dimension exactly r whenever r ≤ sn
-- source:
--   Brakensiek, Chen, Cheraghchi, Goyal, Guruswami, Putterman, Zhang, Explicit Subspace Evasive Sets via Subspace Designs, STOC 2027 submission #312 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/312.pdf, PDF SHA256 a6946cb436bf453cfc53c1547fdd79e55134761b2192ee39f145dfc45490f6bc, Theorem 28, printed p. 14 (PDF p. 15); Definition 27 on the same page

import Definitions.Def_SubspaceEvasion312_Explicit_Supplement_codes

namespace SubspaceEvasion312.Explicit.Supplement
/-- Theorem 28, printed p.14 (PDF p.15). Enc is an encoder of C (linear, image C,
k = dim C). The encoding time T_A + T_Enc is up to one absolute factor K. -/
theorem evasive_subcode :
    ∃ K : ℕ, 0 < K ∧
    ∀ (F : Type) [Field F] [Fintype F] (s n k r c ℓ : ℕ) (R ε ρ : ℝ),
      1 ≤ s → 1 ≤ n → 1 ≤ k → 1 ≤ r → 1 ≤ c → 1 ≤ ℓ → 0 < R → 0 < ε → 0 < ρ →
    ∀ (A : Set (Vec F k)) (C : Code F s n) (E : Vec F k →ₗ[F] Blocks F s n),
      Evasive (F := F) A r c →
      (Fintype.card F : ℝ) ^ ((1 - ε / 2) * k) ≤ (A.ncard : ℝ) →
      IsEncoder C E → R + ε ≤ (k : ℝ) / ((s * n : ℕ) : ℝ) →
      DimensionListRecoverable C ρ ℓ r →
      SetListRecoverable (E '' A) ρ ℓ c ∧ R ≤ setRate (E '' A) ∧
      ∀ (alphabet : Fin (Fintype.card F) ≃ F) (PA PE : Program F) (TA TE BA BE : ℕ),
        Constructable A alphabet PA [] TA BA →
        EvaluatesBlocks PE (fun x => E x) TE BE →
        ∃ (P : Program F) (B : ℕ), B ≤ (BA + BE + TA + TE + 2) ^ K ∧
          EncodableSet (E '' A) alphabet P [] (K * (TA + TE)) B := by sorry
end SubspaceEvasion312.Explicit.Supplement
