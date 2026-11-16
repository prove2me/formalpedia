-- Prove2me | Theorems.Thm_RSCapacity_ListDecoding_Supplement_proximity_gaps_lines
-- name    : RSCapacity.ListDecoding.Supplement.proximity_gaps_lines
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:20:28.08909+00:00
-- url     : https://prove2.me/theorems/5f36f20c-7460-4c08-a933-c7500526b774
-- title:
--   Theorem 1.2 — proximity gaps for lines up to capacity
-- statement:
--   Let $\rho,\varepsilon>0$. There are a constant $C=C(\varepsilon,\rho)>0$ and a threshold $N=N(\varepsilon,\rho)$ such that the following holds. Let $k,n\ge N$ be integers with $k/n\ge\rho$, let $\mathbb F_q$ be any finite field whose characteristic $p$ satisfies $p>k$, let $\alpha_1,\dots,\alpha_n\in\mathbb F_q$ be distinct evaluation points (so $q\ge n$), and let $u,v:\{\alpha_1,\dots,\alpha_n\}\to\mathbb F_q$. Write $\operatorname{agr}(w,f)=\{i\in[n]:w(\alpha_i)=f(\alpha_i)\}$ and $L=n^{C}$. Suppose that for at least $L$ values of $\zeta\in\mathbb F_q$ there is a polynomial $f_\zeta$ of degree less than $k$ with
--
--   $$|\operatorname{agr}(u+\zeta v,f_\zeta)|\ge k(1+\varepsilon).$$
--
--   Then there are polynomials $g,h\in\mathbb F_q[X]$ of degree less than $k$ such that
--
--   $$\bigl|\{i\in[n]: u(\alpha_i)=g(\alpha_i)\ \text{and}\ v(\alpha_i)=h(\alpha_i)\}\bigr|\ge k(1+\varepsilon).$$
--
--   That is, $u$ and $v$ have a common set of at least $k(1+\varepsilon)$ correlated agreements with the Reed–Solomon code $\mathrm{RS}_q[n,k]$; on that set $u+\zeta v$ agrees with $g+\zeta h$ for every $\zeta$. The constant $C$ and the threshold $N$ depend only on $\varepsilon$ and $\rho$: they are fixed before the field, $k$, $n$, the evaluation points and $u,v$.
--
--   This is the proximity-gap counterpart of the mission's goal (Theorem 1.1): if polynomially many members of the line $u+\zeta v$ are within capacity distance $k(1+\varepsilon)$ of the code, then the whole line is, with a single correlated pair $(g,h)$.
--
--   **Formalization Note** $u,v$ are vectors indexed by `Fin n` and $\alpha$ is an injective map `Fin n → F`. "At least $L$ values" compares the cardinality of $\{\zeta\in F:\dots\}$ with the real number $n^C$, and "$\ge k(1+\varepsilon)$" is a real comparison, with no rounding. The characteristic is `ringChar F`.
--
--   Differences from the source:
--   - encoding: functions u, v : E → F_q on the evaluation set E = {α_1, …, α_n} → vectors u, v : Fin n → F with an injective α : Fin n → F; reason: the standing identification of Section 6; same instances
--   - encoding: "k, n large enough positive integers" and "C is some function of ε and ρ" → ∃ C > 0, ∃ N > 0 depending only on ε, ρ, with N ≤ k and N ≤ n; reason: the usual meaning of "large enough"; requiring C > 0 loses nothing because n ≥ 1 makes n^C increasing in C, so any working C can be replaced by max(C, 1)
--   - encoding: q ≥ n → not a separate hypothesis; reason: it is implied by n distinct evaluation points in F_q
--   - reading: restatement on p.20 with "n ≥ k(1+ε) and p ≥ k" → numbered statement on p.2 with p > k and no n ≥ k(1+ε); reason: Theorem 1.2 as numbered on p.2 is authoritative; n ≥ k(1+ε) is implied whenever the premise holds (an agreement count is at most n and L ≥ 1), and p ≥ k is not supported by the proof, whose Lemma 6.6 assumes char(F) > max(k, deg_{Y_i} P)
--   - reading: the "I.e." sentence → not a separate Lean conjunct; reason: it restates the conclusion and its immediate consequence that u + ζv agrees with g + ζh on the common set for every ζ
-- source:
--   Prahladh Harsha, Mrinal Kumar, Ramprasad Saptharishi, STOC 2027 submission #495 (October 2026), Theorem 1.2, p.2 (restated p.20; proof §6 pp.17–23 with Appendices A and C); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/495.pdf

import Mathlib
import Definitions.Def_RSCapacity_ListDecoding_Supplement_ProximityGaps

namespace RSCapacity.ListDecoding.Supplement

open RSCapacity.ListDecoding

/-- Theorem 1.2, submission #495 p.2 (restated p.20): proximity gaps for lines up to
capacity. `C` and the "large enough" threshold `N` depend only on `ε, ρ`; then for
every finite field of characteristic `p > k`, distinct points `α` and `u, v`, if at
least `L = n^C` values `ζ` admit a degree-`< k` polynomial with
`|agr(u + ζ v, f_ζ)| ≥ k(1+ε)`, there are `g, h` of degree `< k` with correlated
agreement at least `k(1+ε)`. -/
theorem proximity_gaps_lines :
    ∀ ρ ε : ℝ, 0 < ρ → 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 0 < N ∧
      ∀ (F : Type) [Field F] [Fintype F] (k n : ℕ) (α u v : Fin n → F),
        N ≤ k → N ≤ n → ρ ≤ (k : ℝ) / n → k < ringChar F →
        Function.Injective α →
        (n : ℝ) ^ C ≤ ({ζ : F | ∃ f : Polynomial F, f.degree < (k : WithBot ℕ) ∧
            (k : ℝ) * (1 + ε) ≤ agreement α (u + ζ • v) f}.ncard : ℝ) →
        ∃ g h : Polynomial F, g.degree < (k : WithBot ℕ) ∧ h.degree < (k : WithBot ℕ) ∧
          (k : ℝ) * (1 + ε) ≤ correlatedAgreement α u v g h := by sorry

end RSCapacity.ListDecoding.Supplement
